"""Static LaTeX, BibTeX & Lean-4 Cross-Reference Auditor for paper/main.tex and paper/references.bib."""
import argparse
from pathlib import Path
import re


def audit_paper(paper_dir: Path, lean_dir: Path | list[Path] | None = None, manuscript: str = "main.tex") -> None:
    tex_path = paper_dir / manuscript
    bib_path = paper_dir / "references.bib"
    tex = tex_path.read_text(encoding="utf-8")
    bib = bib_path.read_text(encoding="utf-8")

    # Strip comments (unescaped %)
    clean = re.sub(r"(?<!\\)%[^\n]*", "", tex)

    # 1. Check balanced \begin{env} ... \end{env}
    stack: list[str] = []
    for m in re.finditer(r"\\(begin|end)\{([^}]+)\}", clean):
        kind, env = m.group(1), m.group(2)
        if kind == "begin":
            stack.append(env)
        else:
            assert stack and stack[-1] == env, f"Mismatched \\end{{{env}}} vs stack {stack}"
            stack.pop()
    assert not stack, f"Unclosed environments: {stack}"

    # 2. Check balanced curly braces in main.tex and references.bib (ignoring \{ and \})
    noback_tex = re.sub(r"\\[{}]", "", clean)
    assert noback_tex.count("{") == noback_tex.count("}"), (
        f"Unbalanced braces in main.tex: {noback_tex.count('{')} vs {noback_tex.count('}')}"
    )
    noback_bib = re.sub(r"\\[{}]", "", bib)
    assert noback_bib.count("{") == noback_bib.count("}"), (
        f"Unbalanced braces in references.bib: {noback_bib.count('{')} vs {noback_bib.count('}')}"
    )

    # 3. Check \[ ... \] balance and inline $ count (outside lstlisting)
    nolst = re.sub(r"\\begin\{lstlisting\}.*?\\end\{lstlisting\}", "", clean, flags=re.DOTALL)
    assert nolst.count(r"\[") == nolst.count(r"\]"), "Unbalanced \\[ \\]"
    inline_dollars = len(re.findall(r"(?<!\\)\$", nolst))
    assert inline_dollars % 2 == 0, f"Odd number of inline $ delimiters: {inline_dollars}"

    # 4. Check labels vs refs/eqrefs (and uniqueness of labels)
    label_list = re.findall(r"\\label\{([^}]+)\}", clean)
    assert len(label_list) == len(set(label_list)), f"Duplicate labels found: {label_list}"
    labels = set(label_list)
    refs = set(re.findall(r"\\(?:eq)?ref\{([^}]+)\}", clean))
    missing_refs = refs - labels
    assert not missing_refs, f"Undefined labels referenced: {missing_refs}"

    # 5. Check citations vs BibTeX keys (both completeness and no unused entries)
    bib_key_list = re.findall(r"@\w+\{([^,\s]+),", bib)
    assert len(bib_key_list) == len(set(bib_key_list)), f"Duplicate BibTeX keys: {bib_key_list}"
    bib_keys = set(bib_key_list)
    cited: set[str] = set()
    for grp in re.findall(r"\\cite\{([^}]+)\}", clean):
        for k in grp.split(","):
            cited.add(k.strip())
    missing_cites = cited - bib_keys
    unused_cites = bib_keys - cited
    assert not missing_cites, f"Missing BibTeX keys: {missing_cites}"
    assert not unused_cites, f"Unused BibTeX keys: {unused_cites}"

    # 6. Cross-check Lean 4 theorem/inductive/macro identifiers if lean_dir is available
    lean_verified_count = 0
    lean_dirs: list[Path] = []
    if isinstance(lean_dir, Path):
        lean_dirs = [lean_dir]
    elif isinstance(lean_dir, list):
        lean_dirs = lean_dir
    for d in lean_dirs:
        assert d.is_dir(), f"Required Lean directory missing: {d}"
        assert any(p for p in d.rglob("*.lean") if ".lake" not in p.parts), f"No Lean source files: {d}"
    existing_lean_dirs = lean_dirs
    if existing_lean_dirs:
        lean_decls: set[str] = set()
        for ldir in existing_lean_dirs:
            for lf in ldir.rglob("*.lean"):
                if ".lake" in lf.parts:
                    continue
                ltxt = lf.read_text(encoding="utf-8")
                for dm in re.finditer(r"^\s*(?:theorem|def|inductive|structure|abbrev)\s+([A-Za-z0-9_']+)", ltxt, re.M):
                    lean_decls.add(dm.group(1))
                for mm in re.finditer(r'macro\s+"([^"]+)"', ltxt):
                    lean_decls.add(mm.group(1).strip())

        tt_spans = [s.replace(r"\_", "_") for s in re.findall(r"\\texttt\{([^}]+)\}", nolst)]
        non_lean_tokens = {
            "cryptid_solve",
            "bbchallenge",
            "mxdys",
            "FAR",
            "CTL",
            "SCEV",
            "PolyQEnt",
            "false",
            "bit_length",
            "autoImplicit = false",
            "0 sorry",
            "0 sorry / 0 admit / 0 axiom",
            "Nat.sub",
            "AppC_1",
            "AppC_5",
            "AppC_6",
            "AppC_7",
            "AppC_8",
            "AppC_1, 7, 8",
            "AppC_1, AppC_7, AppC_8",
            "AppC_5, BMO 7",
            "AppC_6, AppC_8",
            "cryptid_solver_tools.py",
            "verify_all_appendix_a.py",
            "verify_cryptids_suite.py",
            "verify_frontier_holdouts.py",
            "verify_clifford_bridges.py",
            "verify_lean_package.py",
            "phase4_beyond_collatz_toolkit.py",
            "verify_phase4_beyond_collatz.py",
            "lean/CryptidSolve/",
            "lean_interop/",
            "lean_phase4/CryptidSolvePhase4/",
            "lean_phase4/CryptidSolvePhase4",
            "INV65_U64",
            "INV19_U64",
            "native_decide",
            "sorryAx",
        }
        for tok in tt_spans:
            if tok in non_lean_tokens or ".py" in tok or ".lean" in tok or ".c" in tok or "1RB" in tok:
                continue
            if "/" in tok and "_" in tok and "sorry" not in tok:
                prefix_part, rest = tok.split("_", 1)
                for p in prefix_part.split("/"):
                    cand = f"{p}_{rest}"
                    assert cand in lean_decls, f"Shorthand Lean identifier '{cand}' (from '{tok}') not found in {lean_dir}!"
                    lean_verified_count += 1
            elif ("_" in tok or tok.startswith(("State", "inv"))) and re.fullmatch(r"[A-Za-z0-9_']+", tok):
                assert tok in lean_decls, f"Lean identifier '{tok}' cited in main.tex not found in {lean_dir}!"
                lean_verified_count += 1

    print(
        f"[PASS] LaTeX & BibTeX audit passed: "
        f"{len(labels)} unique labels ({len(refs)} refs resolved), "
        f"{len(cited)}/{len(bib_keys)} BibTeX keys matched, "
        f"{lean_verified_count} Lean-4 identifiers cross-verified, "
        f"0 syntax/delimiter errors."
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manuscript", default="main.tex", help="LaTeX filename in paper/")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parent.parent
    audit_paper(repo_root / "paper", [repo_root / "lean", repo_root / "lean_phase4", repo_root / "lean_interop"], args.manuscript)
