# Reproducing the paper

Run the commands from the extracted repository root. Python 3.11 or later covers the Python checks below. They use the standard library. The original PDF and sources are in [paper/](paper/). The file `main.tex` is an earlier interoperability snapshot used by historical regression tests. The paper for this release is `pass1.tex`.

## Verify the copy

```sh
python scripts/verify_release_files.py
```

The manifest gives the SHA-256 of every distributed file except the manifest itself. Source files in the historical proof-build records have their original hashes. Twelve files have editorial changes to source headers for this distribution. The [hash mapping](docs/source-hash-changes.json) lists both values for each changed file. Generated results belong under `results/`.

## Run the paper and finite checks

```sh
python -c "from pathlib import Path; Path('results').mkdir(exist_ok=True)"
python scripts/verify_paper_tex.py --manuscript pass1.tex
python scripts/verify_frontier_holdouts.py --manifest results/phase3.json
python scripts/verify_revision_claims.py --phase3-manifest results/phase3.json
python scripts/generate_appc8_residual_traces.py --check
python scripts/verify_appc8_terminal_grammar.py --output results/terminal-grammar.json
```

The frontier suite counts 5,271 test invocations. The terminal-grammar suite checks 2,220 applications of the tape rules and searches 1,025 single-terminal and 2,050 paired inputs within stated bounds. The Lean build checks the universally quantified statements.

## Build the proof libraries and benchmarks

Docker needs access to its base image, Debian packages, and Lean toolchains for a first build. From the repository root run

```sh
docker build -t bb6-audited .
docker run --rm bb6-audited
```

This builds the two Lean 4.16.0 libraries, runs the kernel axiom checks, runs the Python verification suites, and compiles the C benchmark with GCC. The historical GCC and MSVC timings and compiler versions are listed in the [evidence index](docs/EVIDENCE.md). Timings depend on the host.

For the third library use the same Docker image and a fresh container name. The script downloads the pinned upstream source, Lean 4.35.0-rc4, and its Mathlib cache, then rebuilds the local proofs and their required upstream dependencies. It retains the named container for inspection.

```sh
python -X utf8 scripts/build_interop.py --image bb6-audited --container bb6-interop-reproduction --output results/interop
```

The expected audit totals are 241 integration source theorems and 266 non-internal kernel theorem constants. Both negative controls must be rejected. See the [integration guide](lean_interop/README.md).

## Typeset the paper

Use a LaTeX installation with pdfLaTeX, BibTeX, Latin Modern, microtype, and TikZ. The figures are in the LaTeX source. From the repository root run

```sh
cd paper
pdflatex -halt-on-error -no-shell-escape pass1.tex
bibtex pass1
pdflatex -halt-on-error -no-shell-escape pass1.tex
pdflatex -halt-on-error -no-shell-escape pass1.tex
```

This writes a newly compiled PDF in `paper/`. Use a working copy if you want to preserve the exact bytes of the distributed PDF. PDF timestamps and toolchain versions can affect its checksum.
