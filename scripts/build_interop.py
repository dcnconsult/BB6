"""Reproduce the pinned BB6 interoperability build in an isolated Docker container.
The original Lean 4.16 source files are copied byte-for-byte, never edited.
Mathlib's pinned cache is used; BB6/upstream and adapter modules are rebuilt.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "3647718b5df22e1a61462dec0376bd204526285a"
OUT = ROOT / "docs/audits/interop-latest"
PROJECT = ROOT / "lean_interop"

def command(args, *, log=None, expected=0):
    result = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8", errors="replace")
    if log:
        (OUT / "logs" / log).write_text(output, encoding="utf-8")
    if result.returncode != expected:
        print(output[-12000:])
        raise RuntimeError(f"Command exited {result.returncode}: {args[:4]}")
    return output

def closure():
    names = {"AppC7RawGate", "AppC8RawMod2Sector"}
    done = set()
    while names - done:
        name = sorted(names - done)[0]
        p = ROOT / "lean_phase4/CryptidSolvePhase4" / (name + ".lean")
        names.update(re.findall(r"^import CryptidSolvePhase4\.(\w+)", p.read_text(), re.M))
        done.add(name)
    return [ROOT / "lean_phase4/CryptidSolvePhase4" / (n + ".lean") for n in sorted(done)]

def main():
    global OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--container", default="bb6-interop-rebuild")
    parser.add_argument("--image", default="bb6-cryptid-solve:latest")
    parser.add_argument("--reuse", action="store_true", help="Reuse only the named task container.")
    parser.add_argument("--output", type=Path, default=OUT, help="Audit destination; historical audits are not overwritten by default.")
    args = parser.parse_args()
    OUT = args.output.resolve()
    (OUT / "logs").mkdir(parents=True, exist_ok=True)
    name = args.container
    if not args.reuse:
        command(["docker", "run", "-d", "--name", name, args.image, "sleep", "infinity"])
    def shell(code, **kwargs):
        return command(["docker", "exec", name, "bash", "-c", code], **kwargs)
    def put(path, dest):
        command(["docker", "cp", str(path), name + ":" + dest])
    setup = f"""set -euo pipefail
mkdir -p /work
if [ ! -d /work/cryptids/.git ]; then
  git init /work/cryptids
  git -C /work/cryptids remote add origin https://github.com/google-deepmind/cryptids.git
  git -C /work/cryptids fetch --depth 1 origin {PIN}
  git -C /work/cryptids checkout --detach FETCH_HEAD
fi
cd /work/cryptids
test "$(git rev-parse HEAD)" = "{PIN}"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.35.0-rc4"
elan toolchain install leanprover/lean4:v4.35.0-rc4
lake exe cache get
"""
    # A reused checkout may contain the generated Lake overlay, but no altered upstream proofs.
    setup += "\nchanges=$(git diff --name-only HEAD)\n"
    setup += 'test -z "$changes" || test "$changes" = "lakefile.toml"\n'
    print("Preparing the pinned checkout and dependency cache.", flush=True)
    shell(setup, log="setup.log")
    shell("mkdir -p /work/cryptids/BB6Interop /work/cryptids/CryptidSolvePhase4")
    local_files = closure()
    for p in local_files:
        put(p, "/work/cryptids/CryptidSolvePhase4/" + p.name)
    for p in sorted((PROJECT / "BB6Interop").glob("*.lean")):
        put(p, "/work/cryptids/BB6Interop/" + p.name)
    put(PROJECT / "BB6Interop.lean", "/work/cryptids/BB6Interop.lean")
    put(PROJECT / "LocalImports.lean", "/work/cryptids/CryptidSolvePhase4.lean")
    put(PROJECT / "lake-overlay.toml", "/work/lake-overlay.toml")
    shell("""set -euo pipefail
cd /work/cryptids
git show HEAD:lakefile.toml > /work/lake-original.toml
cat /work/lake-original.toml /work/lake-overlay.toml > lakefile.toml
""")
    print("Rebuilding the pinned upstream dependency and adapter source.", flush=True)
    shell("""set -euo pipefail
cd /work/cryptids
lake clean Cryptids
lake build BB6Interop BB6Interop.KernelAudit
""", log="clean-build-and-axioms.log")
    audit = (PROJECT / "BB6Interop/KernelAudit.lean").read_text()
    fixtures = {
        "foreign-axiom": "namespace ForeignFixture\naxiom untrusted : False\nend ForeignFixture\n"
            "theorem BB6Interop.badFixture : False := ForeignFixture.untrusted\n",
        "sorry": "theorem BB6Interop.badFixture : False := by sorry\n",
    }
    scratch = OUT / "negative-fixtures"
    scratch.mkdir(exist_ok=True)
    for label, body in fixtures.items():
        f = scratch / (label + ".lean")
        f.write_text(audit.replace("open Lean in\n", body + "\nopen Lean in\n", 1), encoding="utf-8")
        put(f, "/work/cryptids/NegativeFixture.lean")
        result = subprocess.run(["docker", "exec", name, "bash", "-c",
            "cd /work/cryptids; lake env lean NegativeFixture.lean"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = result.stdout.decode("utf-8", errors="replace")
        (OUT / "logs" / ("negative-" + label + ".log")).write_text(output, encoding="utf-8")
        assert result.returncode != 0 and "non-allowlisted axiom" in output, output[-4000:]
    env = shell("cd /work/cryptids; lean --version; lake --version; git rev-parse HEAD; git diff -- lakefile.toml")
    env += command(["docker", "inspect", "--format", "{{.Image}}", name])
    (OUT / "logs/environment.log").write_text(env, encoding="utf-8")
    command(["docker", "cp", name + ":/work/cryptids/lake-manifest.json", str(OUT / "upstream-lake-manifest.json")])
    sources = local_files + sorted(PROJECT.rglob("*.lean")) + [PROJECT / "lake-overlay.toml", Path(__file__)]
    hashes = {str(p.relative_to(ROOT)).replace("\\", "/"): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    # Confirm the copied canonical source bytes match the compiled inputs.
    remote = shell("cd /work/cryptids; sha256sum " + " ".join("CryptidSolvePhase4/" + p.name for p in local_files))
    for line in remote.splitlines():
        digest, path = line.split()
        assert digest == hashes["lean_phase4/" + path], path
    source_count = sum(len(re.findall(r"^\s*(?:@\[simp\]\s*)?theorem\s", p.read_text(), re.M))
                       for p in (PROJECT / "BB6Interop").glob("*.lean"))
    build_log = (OUT / "logs/clean-build-and-axioms.log").read_text()
    match = re.search(r"INTEROP AUDIT PASS: (\d+) non-internal theorem constants", build_log)
    assert match, "Missing successful kernel audit"
    result = {"upstream_commit": PIN, "lean": "4.35.0-rc4",
              "adapter_source_theorems": source_count, "adapter_kernel_theorems": int(match[1]),
              "allowed_transitive_axioms": ["propext", "Quot.sound", "Classical.choice"],
              "negative_foreign_axiom_rejected": True, "negative_sorry_rejected": True,
              "canonical_local_sources_copied_unchanged": True,
              "local_dependency_files": len(local_files), "source_sha256": hashes,
              "scope": "Compiled adapter plus required upstream dependency closure; pinned Mathlib cache used."}
    (OUT / "build-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {source_count} source theorems; {match[1]} kernel constants; both negative controls rejected.",
          flush=True)

if __name__ == "__main__":
    main()
