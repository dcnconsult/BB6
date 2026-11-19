# syntax=docker/dockerfile:1
# Reproducible Artifact Image for BB(6) Phases 1-4:
#   - Phases 1-3: Collatz Cryptids (`lean/CryptidSolve`, `scripts/`, `benchmarks/`)
#   - Phase 4:    BB6 algebraic examples and tape-level proofs
#                 (`lean_phase4/CryptidSolvePhase4`, `scripts/verify_phase4_beyond_collatz.py`)

FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive \
    ELAN_HOME=/usr/local/elan \
    PATH="/usr/local/elan/bin:${PATH}"

# 1. Minimal system dependencies (elan/Lean 4, GCC -O3 for C11 benchmarks, Python 3 for zero-float verifiers)
RUN apt-get update && apt-get install -y --no-install-recommends \
        bash \
        ca-certificates \
        curl \
        gcc \
        git \
        libc6-dev \
        python3 \
    && rm -rf /var/lib/apt/lists/*

# 2. Install elan & pinned Lean 4.16.0 toolchain (shared by both `lean/` and `lean_phase4/`)
COPY lean_phase4/lean-toolchain /tmp/lean-toolchain
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain "$(cat /tmp/lean-toolchain | tr -d '\r\n')" \
    && lean --version \
    && lake --version

WORKDIR /workspace

# 3a. Copy and kernel-check the sealed Phase 1-3 Lean 4 CryptidSolve library
COPY lean/lean-toolchain lean/lakefile.lean lean/CryptidSolve.lean /workspace/lean/
COPY lean/CryptidSolve/ /workspace/lean/CryptidSolve/
RUN cd /workspace/lean && lake build

# 3b. Copy source-only Phase 4 Lean 4 CryptidSolvePhase4 files (excluding any host `.lake/`) and kernel-check
COPY lean_phase4/lean-toolchain /workspace/lean_phase4/lean-toolchain
COPY lean_phase4/lakefile.lean /workspace/lean_phase4/lakefile.lean
COPY lean_phase4/CryptidSolvePhase4.lean /workspace/lean_phase4/CryptidSolvePhase4.lean
COPY lean_phase4/CryptidSolvePhase4/ /workspace/lean_phase4/CryptidSolvePhase4/
RUN cd /workspace/lean_phase4 && lake build

# 4. Copy scripts, benchmarks, paper, and docs for full end-to-end Phase 1-4 verification
COPY scripts/ /workspace/scripts/
COPY benchmarks/ /workspace/benchmarks/
COPY paper/ /workspace/paper/
# Sources for manuscript identifier checks; build the interoperability overlay separately.
COPY lean_interop/ /workspace/lean_interop/
COPY docs/ /workspace/docs/
COPY README.md /workspace/README.md
COPY docker/verify_all.sh /usr/local/bin/verify_all.sh
COPY docker/verify_phase4.sh /usr/local/bin/verify_phase4.sh
RUN sed -i 's/\r$//' /usr/local/bin/verify_all.sh /usr/local/bin/verify_phase4.sh \
    && chmod +x /usr/local/bin/verify_all.sh /usr/local/bin/verify_phase4.sh

CMD ["/usr/local/bin/verify_phase4.sh"]
