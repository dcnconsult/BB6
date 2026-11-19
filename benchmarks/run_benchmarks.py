"""
Build, execute, inspect x86-64 assembly, and benchmark C11 (MSVC /O2 /arch:AVX2 or Clang/GCC -O3)
and Python 3.14 BigInt acceleration for Transfer #2:
O(1) Scalar Loop Summarization via p-Adic Ghost Shifts (TZCNT / LZCNT).
"""

from pathlib import Path
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time


def find_msvc_and_sdk():
    vs_roots = [
        Path(r"C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\VC\Tools\MSVC"),
        Path(r"C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC"),
        Path(r"C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC"),
    ]
    msvc_dir = None
    for root in vs_roots:
        if root.exists():
            versions = sorted([p for p in root.iterdir() if p.is_dir()])
            for cand in reversed(versions):
                if (cand / "bin" / "Hostx64" / "x64" / "cl.exe").exists():
                    msvc_dir = cand
                    break
        if msvc_dir is not None:
            break

    kits_root = Path(r"C:\Program Files (x86)\Windows Kits\10")
    sdk_ver = None
    if (kits_root / "Include").exists():
        sdks = sorted([p.name for p in (kits_root / "Include").iterdir() if p.is_dir() and p.name.startswith("10.")])
        if sdks:
            sdk_ver = sdks[-1]
    return msvc_dir, kits_root, sdk_ver


def build_c_benchmark(c_src: Path, build_dir: Path) -> tuple[Path, Path | None, str]:
    build_dir.mkdir(parents=True, exist_ok=True)
    msvc_dir, kits_root, sdk_ver = find_msvc_and_sdk()
    if msvc_dir is not None and sdk_ver is not None:
        env = os.environ.copy()
        env["INCLUDE"] = os.pathsep.join([
            str(msvc_dir / "include"),
            str(kits_root / "Include" / sdk_ver / "ucrt"),
            str(kits_root / "Include" / sdk_ver / "shared"),
            str(kits_root / "Include" / sdk_ver / "um"),
        ])
        env["LIB"] = os.pathsep.join([
            str(msvc_dir / "lib" / "x64"),
            str(kits_root / "Lib" / sdk_ver / "ucrt" / "x64"),
            str(kits_root / "Lib" / sdk_ver / "um" / "x64"),
        ])
        env["PATH"] = os.pathsep.join([
            str(msvc_dir / "bin" / "Hostx64" / "x64"),
            str(kits_root / "bin" / sdk_ver / "x64"),
            env.get("PATH", ""),
        ])
        cl_exe = msvc_dir / "bin" / "Hostx64" / "x64" / "cl.exe"
        exe_path = build_dir / "clz_ctz_bench.exe"
        obj_path = build_dir / "clz_ctz_bench.obj"
        cod_path = build_dir / "clz_ctz_bench.cod"
        cmd = [
            str(cl_exe),
            "/O2",
            "/Oi",
            "/arch:AVX2",
            f"/Fa{cod_path}",
            "/FAcs",
            str(c_src),
            f"/Fe:{exe_path}",
            f"/Fo:{obj_path}",
        ]
        res = subprocess.run(cmd, env=env, cwd=str(build_dir), capture_output=True, text=True)
        if res.returncode != 0:
            raise RuntimeError(f"MSVC build failed:\n{res.stdout}\n{res.stderr}")
        compiler_banner = res.stderr.splitlines()[0].strip() if res.stderr else f"MSVC {msvc_dir.name}"
        return exe_path, cod_path, compiler_banner

    for cc in ("clang", "gcc"):
        cc_bin = shutil.which(cc)
        if cc_bin:
            exe_path = build_dir / ("clz_ctz_bench.exe" if os.name == "nt" else "clz_ctz_bench")
            cmd = [cc_bin, "-O3", "-march=native", str(c_src), "-o", str(exe_path)]
            res = subprocess.run(cmd, cwd=str(build_dir), capture_output=True, text=True)
            if res.returncode != 0:
                raise RuntimeError(f"{cc} build failed:\n{res.stderr}")
            ver = subprocess.run([cc_bin, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
            return exe_path, None, ver

    raise RuntimeError("No C compiler (MSVC cl, clang, or gcc) found!")


def analyze_msvc_cod(cod_path: Path) -> list[dict]:
    """Parse MSVC /FAcs .cod listing to audit instructions and loop back-edges per kernel."""
    txt = cod_path.read_text(encoding="utf-8", errors="replace")
    fn_names = [
        "k1_antihydra_tneg1_naive",
        "k1_antihydra_tneg1_ghost",
        "k2_antihydra_odd_naive",
        "k2_antihydra_odd_ghost",
        "k3_antihydra_t0_naive",
        "k3_antihydra_t0_ghost",
        "k4_cousin_a2_a10_naive",
        "k4_cousin_a2_a10_ghost",
        "k5_cousin_a5_naive",
        "k5_cousin_a5_ghost",
        "k6_appc1_chained_naive",
        "k6_appc1_chained_ghost",
    ]
    stats = []
    for fn in fn_names:
        m = re.search(rf"^{re.escape(fn)}\s+PROC.*?(?=^{re.escape(fn)}\s+ENDP)", txt, re.M | re.S)
        if not m:
            continue
        body = m.group(0)
        insns = []
        labels_seen = set()
        backward_jumps = 0
        cond_jumps = 0
        tzcnt_cnt = 0
        lzcnt_cnt = 0
        div_cnt = 0
        joined_body = re.sub(r"\n\t([0-9a-fA-F]{2}(?:\s+[0-9a-fA-F]{2})*)\s+", r" \1 ", body)
        for line in joined_body.splitlines():
            lm = re.match(r"^(\$[A-Za-z0-9_@]+):", line.strip())
            if lm:
                labels_seen.add(lm.group(1))
                continue
            im = re.match(r"^\s*[0-9a-fA-F]{5}\s+[0-9a-fA-F]{2}(?:\s+[0-9a-fA-F]{2})*\s+([a-z][a-z0-9]*)\b(.*)$", line)
            if im:
                op = im.group(1).lower()
                rest = im.group(2).split(";")[0].strip()
                if op in ("nop", "npad"):
                    continue
                insns.append((op, rest))
                if op == "tzcnt":
                    tzcnt_cnt += 1
                elif op == "lzcnt":
                    lzcnt_cnt += 1
                elif op in ("div", "idiv"):
                    div_cnt += 1
                elif op.startswith("j"):
                    if op != "jmp":
                        cond_jumps += 1
                    tgt = rest.split()[-1] if rest else ""
                    if tgt in labels_seen:
                        backward_jumps += 1
        stats.append({
            "fn": fn,
            "insns": len(insns),
            "tzcnt": tzcnt_cnt,
            "lzcnt": lzcnt_cnt,
            "div": div_cnt,
            "cond_jumps": cond_jumps,
            "backward_loops": backward_jumps,
        })
    return stats


def run_python_bigint_benchmarks() -> list[dict]:
    """Benchmark Python 3.14 arbitrary-precision Ghost Shift vs Naive Loop (up to 256-bit integers)."""
    results = []
    n_items = 4000
    odd_inputs = [((3 * (i % 7 + 1)) << ((i % 120) + 20)) - 1 for i in range(n_items)]
    c_budget = 500

    def py_odd_naive(arr):
        acc = 0
        for z in arr:
            c = c_budget
            while (z & 1) == 1 and c >= 1:
                z = (3 * z + 1) >> 1
                c -= 1
            acc ^= (z & 0xFFFFFFFFFFFFFFFF) ^ c
        return acc

    pow3 = [3**k for k in range(160)]

    def py_odd_ghost(arr):
        acc = 0
        for z in arr:
            phi = z + 1
            m_val = (phi & -phi).bit_length() - 1
            m = m_val if m_val < c_budget else c_budget
            z = pow3[m] * (phi >> m) - 1
            c = c_budget - m
            acc ^= (z & 0xFFFFFFFFFFFFFFFF) ^ c
        return acc

    assert py_odd_naive(odd_inputs[:200]) == py_odd_ghost(odd_inputs[:200])
    t0 = time.perf_counter()
    c1 = py_odd_naive(odd_inputs)
    t_naive = time.perf_counter() - t0
    t0 = time.perf_counter()
    c2 = py_odd_ghost(odd_inputs)
    t_ghost = time.perf_counter() - t0
    assert c1 == c2
    py_ver = f"Py{sys.version_info.major}.{sys.version_info.minor}"
    results.append({
        "name": f"{py_ver} BigInt CTZ (Antihydra Odd-Run, m in 20..139)",
        "mean_steps": sum(((i % 120) + 20) for i in range(n_items)) / n_items,
        "us_naive": (t_naive * 1e6) / n_items,
        "us_ghost": (t_ghost * 1e6) / n_items,
        "speedup": t_naive / t_ghost,
    })

    a5_inputs = []
    for i in range(n_items):
        L = (i % 64) + 2
        j_t = (i % 160) + 30
        U0 = L + 5
        R = ((2 * U0) << j_t) - 2 * U0 - 7 * (j_t - 1) - 5
        a5_inputs.append((L, R))

    def py_a5_naive(arr):
        acc = 0
        for L, R in arr:
            j = 0
            while R >= 2 * L + 3:
                R -= (2 * L + 3)
                L = 2 * L + 5
                j += 1
            acc ^= (L & 0xFFFFFFFFFFFFFFFF) ^ (R & 0xFFFFFFFFFFFFFFFF) ^ j
        return acc

    def py_a5_ghost(arr):
        acc = 0
        for L, R in arr:
            if R < 2 * L + 3:
                j = 0
            else:
                U0 = L + 5
                W = R + 2 * U0 + 7
                j = W.bit_length() - U0.bit_length() - 2
                if R >= ((2 * U0) << (j + 1)) - 2 * U0 - 7 * j - 7:
                    j += 1
                if R >= ((2 * U0) << (j + 1)) - 2 * U0 - 7 * j - 7:
                    j += 1
                Uj = U0 << j
                R -= 2 * (Uj - U0) - 7 * j
                L = Uj - 5
            acc ^= (L & 0xFFFFFFFFFFFFFFFF) ^ (R & 0xFFFFFFFFFFFFFFFF) ^ j
        return acc

    assert py_a5_naive(a5_inputs[:200]) == py_a5_ghost(a5_inputs[:200])
    t0 = time.perf_counter()
    c1 = py_a5_naive(a5_inputs)
    t_naive = time.perf_counter() - t0
    t0 = time.perf_counter()
    c2 = py_a5_ghost(a5_inputs)
    t_ghost = time.perf_counter() - t0
    assert c1 == c2
    py_ver = f"Py{sys.version_info.major}.{sys.version_info.minor}"
    results.append({
        "name": f"{py_ver} BigInt CLZ (Cryptid A.5 Doubler, j in 30..189)",
        "mean_steps": sum(((i % 160) + 30) for i in range(n_items)) / n_items,
        "us_naive": (t_naive * 1e6) / n_items,
        "us_ghost": (t_ghost * 1e6) / n_items,
        "speedup": t_naive / t_ghost,
    })
    return results


def main():
    here = Path(__file__).resolve().parent
    c_src = here / "clz_ctz_bench.c"
    build_dir = Path(tempfile.gettempdir()) / "bb6_clz_ctz_bench_build"

    print(f"Host Python: {sys.version.splitlines()[0]}")
    print(f"Host CPU:    {platform.processor()} ({os.cpu_count()} logical cores)")

    exe_path, cod_path, compiler_banner = build_c_benchmark(c_src, build_dir)
    print(f"C Compiler:  {compiler_banner}")
    opt_label = "/O2 /Oi /arch:AVX2" if cod_path is not None else "-O3 -march=native"

    run_res = subprocess.run([str(exe_path)], capture_output=True, text=True)
    if run_res.returncode != 0:
        raise RuntimeError(f"Benchmark binary failed:\nSTDOUT:\n{run_res.stdout}\nSTDERR:\n{run_res.stderr}")

    print(f"\n=== C11 Hardware Benchmark Output ({opt_label}) ===")
    for line in run_res.stdout.strip().splitlines():
        print(line)

    if cod_path is not None and cod_path.exists():
        print("\n=== x86-64 Machine-Code Audit (MSVC /FAcs Listing) ===")
        for st in analyze_msvc_cod(cod_path):
            print(
                f"ASM|{st['fn']:28s}|insns={st['insns']:2d}|tzcnt={st['tzcnt']}|lzcnt={st['lzcnt']}|"
                f"div={st['div']}|cond_br={st['cond_jumps']}|back_loops={st['backward_loops']}"
            )

    py_ver = f"{sys.version_info.major}.{sys.version_info.minor}"
    print(f"\n=== Python {py_ver} Arbitrary-Precision BigInt Benchmark ===")
    for r in run_python_bigint_benchmarks():
        print(
            f"PY|{r['name']}|mean_steps={r['mean_steps']:.1f}|"
            f"naive={r['us_naive']:.3f} us|ghost={r['us_ghost']:.3f} us|speedup={r['speedup']:.2f}x"
        )


if __name__ == "__main__":
    main()
