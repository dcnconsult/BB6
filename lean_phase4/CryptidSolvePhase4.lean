/-
  CryptidSolvePhase4 — Phase 4 Beyond-Collatz Algebraic Transfers
  ============================================================================================
  Zero-dependency pure Lean 4 Core (`Init` + `omega` + `decide`, `0 sorryAx`, `0` custom axioms)
  formalization of all seven Beyond-Collatz algebraic transfers:

    - `Basic`                       : `StepFn`, `IsInvariant`, `IsNonHalting`, `IsImmortalOrbit`,
                                      safe-invariant, Prajna-Jadbabaie barrier, & integer drift meta-theorems.
    - `Transfer1MatrixMonoid`       : Non-abelian `Mat2Int` monoid lifts separating variable-arity
                                      `AppC_7` multi-defect configurations (`T^4 D^2 ≠ D^2 T^4`)
                                      where abelian Parikh / `H_1` projections are blind.
    - `Transfer2PutinarSOS`         : Exact integer-cleared rational `LDL^T` Putinar SOS barriers
                                      (`Stage 3c`), affine-barrier impossibility on parabolic counters,
                                      and `AppC_7`'s `16b^2 + 28b + 15` quadratic gate law.
    - `Transfer3PisotQuadratic`     : Exact `Z[phi]` / `Z[sqrt 2]` Galois norm barriers proving
                                      immortality where **100% of finite modular sieves (`M ≥ 1`) fail**.
    - `Transfer4WreathBlockGauge`   : `F_2` coboundary loop invariance, `[7,4,3]` Hamming gauge coset,
                                      Width-3 Wreath Odometer immortality, and `AppC_8`'s exact width-3
                                      shuttle & `108q^2 + 332q + 238` `(3/2)`-Collatz ghost `c* = -4`.
    - `Transfer5SpaceTimeCohomology`: 2D cochain exactness `d1 ∘ d0 = 0`, 2D Discrete Stokes' Theorem,
                                      3-cell NFA 3-step failure witness, and unconditional raw-tape
                                      non-halting of `1RB0RF_0RE0RE_1RF1LD_0LC0LA_0LD1RF_0LA---`.
    - `Transfer6MolienAndWalkSeries`: Reynolds/Molien symmetry degree predictors and rational
                                      walk series denominators `Q(t)` across 4 `BB(6)` dynamical regimes.
    - `Transfer7MultiPrimeKirchhoff`: Multi-prime CRT `{2, 3}` & `{3, 7}` local-global portal eliminations
                                      (where constituent prime powers fail) and Antihydra Mod-8 exact
                                      integer-cleared Laplacian pseudoinverse `48 * L^+` (`R_eff = 29/48`).
-/

import CryptidSolvePhase4.Basic
import CryptidSolvePhase4.Transfer1MatrixMonoid
import CryptidSolvePhase4.Transfer2PutinarSOS
import CryptidSolvePhase4.AppC7RawGate
import CryptidSolvePhase4.Transfer3PisotQuadratic
import CryptidSolvePhase4.Transfer4WreathBlockGauge
import CryptidSolvePhase4.AppC8RawShuttle
import CryptidSolvePhase4.AppC8RawCleanMacro
import CryptidSolvePhase4.AppC8RawBlankReachability
import CryptidSolvePhase4.AppC8RawOddSector
import CryptidSolvePhase4.AppC8RawMod2Sector
import CryptidSolvePhase4.Transfer5SpaceTimeCohomology
import CryptidSolvePhase4.Transfer6MolienAndWalkSeries
import CryptidSolvePhase4.Transfer7MultiPrimeKirchhoff
