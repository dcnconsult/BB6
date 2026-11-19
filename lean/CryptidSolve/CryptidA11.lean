/-
  CryptidSolve.CryptidA11
  =======================
  Counter-model formalization and finite epoch evaluations for Cryptid A.11
  (`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`):
    1. Exact 4-parameter macro-transition rules `C(a,b,c,d)`, `M(r,b,c,d)`, `L(r,b,d)`.
    2. Universal Homogenization Lemma (`a11_homogenize_two_step`): proves
       `X(a, 3q) = a + 2q + 12` reduces every 2-step sweep (`c ≥ 2`) to `f(X) = ⌊3X / 2⌋`
       uniformly across all `b = 3q` (`b ∈ {0, 3, 6, ...}`).
    3. Complete 4-sector 1D epoch return map `epochStepA11` (including `d = 6`).
    4. Kernel-evaluated Epoch 0 → Epoch 1 → Epoch 2 → Epoch 3 → Epoch 4 resolution:
       - `fIter 569 20 % 8 = 7` (`% 4 = 3`),
       - `epochStepA11 (20, 1138, 3) = some (20, c4_exact, 3)` (survives Epoch 3!),
       - `c4_exact % 2 = 1` (`c_4` is strictly ODD!),
       - If Epoch 4 returns a successor, that successor has `d = 6`.
  No general aperiodicity, Epoch-4 completion, or raw-to-macro refinement theorem is asserted.
-/

import CryptidSolve.Tactic

namespace CryptidSolve

/-! ## 1. Exact Macro-Configurations & Rules -/

inductive ConfigA11 where
  | C (a b c d : Nat)
  | M (r b c d : Nat)
  | L (r b d : Nat)
  deriving DecidableEq, Repr

def stepMacroA11 : ConfigA11 → Option ConfigA11
  | .C a b 0 6 => some (.C a (b + 3) 0 3)
  | .C a b c d => some (.M (a % 2) (b + 3 * (a / 2)) c d)
  | .M r b' (c + 2) d => some (.C (r + b' + 4) 3 c d)
  | .M r b' 1 6 => some (.C (r + b' + 4) 0 3 3)
  | .M r b' 0 3 => some (.L r (b' + 1) 3)
  | .M r b' 1 3 => some (.L r b' 6)
  | .M _ _ _ _ => none
  | .L 0 b d =>
      if b % 2 = 0 then none
      else some (.C 0 0 (b / 2 + 3) d)
  | .L _ b d =>
      if b = 0 then
        if d = 3 then none else some (.C 6 0 3 3)
      else if b % 2 = 1 then
        some (.C 1 0 (b / 2 + 3) d)
      else
        some (.C 6 3 (b / 2 - 1) d)

/-! ## 2. Universal Homogenization Lemma (`X(a, 3q) = a + 2q + 12`) -/

def homogX (a q : Nat) : Nat := a + 2 * q + 12

def fA11 (x : Nat) : Nat := (3 * x) / 2

/-- Tail-recursive `m`-step iteration of `f(X) = ⌊3X / 2⌋` for fast kernel evaluation. -/
def fIter : Nat → Nat → Nat
  | 0, x => x
  | m + 1, x => fIter m (fA11 x)

theorem fIter_ge_self : ∀ m x, x ≤ fIter m x
  | 0, _ => by simp [fIter]
  | m + 1, x => by
      simp only [fIter]
      have hx : x ≤ fA11 x := by unfold fA11; omega
      have ih := fIter_ge_self m (fA11 x)
      omega

/-- Lemma 3.1 (Universal Homogenization):
    Across any `c + 2` sweep step from `C(a, 3q, c + 2, d)`, two macro-steps reach
    `C(a', 3, c, d)` whose homogenized coordinate `homogX a' 1` equals `fA11 (homogX a q)`
    identically—eliminating all boundary case-splits between `b = 0`, `3`, and `6`. -/
theorem a11_homogenize_two_step (a q c d : Nat) :
    ∃ a', iterStep stepMacroA11 2 (.C a (3 * q) (c + 2) d) = some (.C a' 3 c d) ∧
          homogX a' 1 = fA11 (homogX a q) := by
  refine ⟨a % 2 + (3 * q + 3 * (a / 2)) + 4, ?_, ?_⟩
  · rfl
  · unfold homogX fA11
    omega

/-! ## 3. Complete 4-Sector 1D Epoch Return Map (Including `d = 6`) -/

def dispatchLA11 (r bEnd dOut : Nat) : Option (Nat × Nat × Nat) :=
  if r = 0 then
    if bEnd % 2 = 0 then none
    else some (12, (bEnd + 5) / 2, dOut)
  else
    if bEnd = 0 then
      if dOut = 3 then none else some (18, 3, 3)
    else if bEnd % 2 = 1 then
      some (13, (bEnd + 5) / 2, dOut)
    else
      some (20, (bEnd - 2) / 2, dOut)

/-- Exact 1D epoch return map `(X0, c, d) ↦ Option (X0', c', d')` for `X0 ≥ 12, d ∈ {3, 6}`. -/
def epochStepA11 (ep : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  let X0 := ep.1
  let c := ep.2.1
  let d := ep.2.2
  let Z := fIter (c / 2) X0
  if c % 2 = 1 ∧ d = 6 then
    some (fA11 Z - 2, 3, 3)
  else if c % 2 = 0 ∧ d = 3 then
    dispatchLA11 (Z % 2) (3 * (Z / 2) - 17) 3
  else if c % 2 = 0 ∧ d = 6 then
    dispatchLA11 (Z % 2) (3 * (Z / 2) - 14) 3
  else
    dispatchLA11 (Z % 2) (3 * (Z / 2) - 18) 6

/-! ## 4. Exact Epoch-3 Evaluation and Conditional Subsequent `d = 6` Activation -/

/-- Blank-tape trajectory across Epochs 0, 1, and 2:
    `(16, 0, 3) → (12, 6, 3) → (12, 24, 3) → (20, 1138, 3)`. -/
theorem a11_epochs_0_to_3 :
    iterStep epochStepA11 3 (16, 0, 3) = some (20, 1138, 3) := by
  decide

/-- Exact 102-digit integer `Z_3 = f^{569}(20)`. -/
def Z3_exact : Nat :=
  308839082650318263084746811144577298419438349956846904254255829450012113426945746099328526614386747919

/-- Exact 102-digit Epoch-4 counter `c_4 = (3 * ⌊Z_3 / 2⌋ - 19) / 2`. -/
def c4_exact : Nat :=
  231629311987738697313560108358432973814578762467635178190691872087509085070209309574496394960790060929

set_option maxRecDepth 100000 in
/-- Kernel big-integer verification of `f^{569}(20)` and its Mod-8 / Mod-4 residues. -/
theorem a11_Z3_eval_and_residues :
    fIter 569 20 = Z3_exact ∧ fIter 569 20 % 8 = 7 ∧ fIter 569 20 % 4 = 3 := by
  decide

set_option maxRecDepth 100000 in
/-- Theorem 3.2 (Epoch-3 Survival & Odd `c_4` Theorem):
    Cryptid A.11 survives Epoch 3 (`(20, 1138, 3)`) into `(20, c4_exact, 3)` with
    `c4_exact` strictly ODD (`c4_exact % 16 = 1`). -/
theorem a11_epoch3_survives_with_odd_c4 :
    epochStepA11 (20, 1138, 3) = some (20, c4_exact, 3) ∧
    c4_exact % 2 = 1 ∧
    c4_exact % 16 = 1 := by
  decide

/-- Deterministic `d = 6` Sector Activation Theorem:
    Every surviving epoch from `(X0, c, 3)` with `X0 ≥ 14` and `c` odd (`c % 2 = 1`,
    such as Epoch 4 `(20, c4_exact, 3)`) transitions into `d' = 6` (`ep'.2.2 = 6`). -/
theorem a11_odd_c_activates_d6 (X0 c : Nat) (ep' : Nat × Nat × Nat)
    (hX0 : X0 ≥ 14)
    (hcOdd : c % 2 = 1)
    (hSurv : epochStepA11 (X0, c, 3) = some ep') :
    ep'.2.2 = 6 := by
  have hZ : 14 ≤ fIter (c / 2) X0 := by
    have hMono := fIter_ge_self (c / 2) X0
    omega
  dsimp only [epochStepA11, dispatchLA11] at hSurv
  generalize fIter (c / 2) X0 = Z at hZ hSurv
  cryptid_step_omega hSurv

end CryptidSolve
