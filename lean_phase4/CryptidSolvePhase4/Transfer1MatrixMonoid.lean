/-
  CryptidSolvePhase4.Transfer1MatrixMonoid
  ========================================
  Transfer 1:
  From `p = 6` Abelian Parikh Counters (`N^D`) to Non-Abelian Matrix Monoid Lifts
  (`mu : Sigma* -> Mat_2(Z)` / `Non-Abelian Matrix CTL*`).

  Formalizes:
    1. Exact `2 x 2` integer matrix monoid `Mat2Int` (`mul_assoc`, `id_mul`, `mul_id`).
    2. Arbitrary-arity multi-defect tape word homomorphism `wordLift : List DefectSym -> Mat2Int`
       with non-commuting generators `T -> [[1, 1], [0, 1]]` and `D -> [[17, 7], [0, 4]]`
       (`wordLift (u ++ v) = mul (wordLift u) (wordLift v)`).
    3. Abelian Parikh Blindness vs. Non-Abelian Matrix Separation (`T^4 D^2` vs. `D^2 T^4`
       share identical Parikh counts `(4, 2)` yet evaluate to `[[289, 211], [0, 16]]` vs.
       `[[289, 1303], [0, 16]]`, matching raw `AppC_7` condensation `31 != 22`).
    4. Context-Independent Non-Abelian Matrix Cone Monotonicity (`wordLift_context_rewrite_monotone`):
       any local rewrite `u -> v` inside an arbitrary multi-defect tape `p ++ u ++ s` of
       unbounded defect count `r -> infinity` strictly advances `(wordLift (p ++ v ++ s)).m01`,
       certifying `IsImmortalOrbit` on unbounded multi-defect rewrite machines without fixing
       counter dimension `D`.
-/

import CryptidSolvePhase4.Basic

namespace CryptidSolvePhase4

/-! ## 1. Exact `2 x 2` Integer Matrix Monoid -/

/-- `2 x 2` matrix `[[m00, m01], [m10, m11]]` over `Int`. -/
structure Mat2Int where
  m00 : Int
  m01 : Int
  m10 : Int
  m11 : Int
  deriving DecidableEq, Repr

namespace Mat2Int

def id : Mat2Int := ⟨1, 0, 0, 1⟩

def add (A B : Mat2Int) : Mat2Int :=
  ⟨A.m00 + B.m00, A.m01 + B.m01, A.m10 + B.m10, A.m11 + B.m11⟩

def sub (A B : Mat2Int) : Mat2Int :=
  ⟨A.m00 - B.m00, A.m01 - B.m01, A.m10 - B.m10, A.m11 - B.m11⟩

def mul (A B : Mat2Int) : Mat2Int :=
  ⟨A.m00 * B.m00 + A.m01 * B.m10,
   A.m00 * B.m01 + A.m01 * B.m11,
   A.m10 * B.m00 + A.m11 * B.m10,
   A.m10 * B.m01 + A.m11 * B.m11⟩

def trace (A : Mat2Int) : Int :=
  A.m00 + A.m11

def det (A : Mat2Int) : Int :=
  A.m00 * A.m11 - A.m01 * A.m10

theorem id_mul (A : Mat2Int) : mul id A = A := by
  cases A
  unfold mul id
  simp only [Mat2Int.mk.injEq, Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add, and_self]

theorem mul_id (A : Mat2Int) : mul A id = A := by
  cases A
  unfold mul id
  simp only [Mat2Int.mk.injEq, Int.mul_one, Int.mul_zero, Int.add_zero, Int.zero_add, and_self]

theorem mul_assoc (A B C : Mat2Int) : mul (mul A B) C = mul A (mul B C) := by
  unfold mul
  simp only [Mat2Int.mk.injEq, Int.add_mul, Int.mul_add, ← Int.mul_assoc]
  exact ⟨by omega, by omega, by omega, by omega⟩

end Mat2Int

/-! ## 2. Multi-Defect Tape Alphabet, Abelian Parikh Shadow & Non-Abelian Matrix Lift -/

/-- Macro-alphabet for variable-arity multi-defect tapes (e.g., `AppC_7` `(10)` vs `(11100)`). -/
inductive DefectSym where
  | T
  | D
  deriving DecidableEq, Repr

/-- Abelian `H_1` / Parikh projection `(count_T, count_D)` forgetting defect order. -/
def parikhCount : List DefectSym → Nat × Nat
  | [] => (0, 0)
  | .T :: rest =>
      let p := parikhCount rest
      (p.1 + 1, p.2)
  | .D :: rest =>
      let p := parikhCount rest
      (p.1, p.2 + 1)

/-- Non-abelian generator assignment:
    `T ↦ [[1, 1], [0, 1]]` (unit translation), `D ↦ [[17, 7], [0, 4]]` (defect affine scaling). -/
def symMatrix : DefectSym → Mat2Int
  | .T => ⟨1, 1, 0, 1⟩
  | .D => ⟨17, 7, 0, 4⟩

/-- Non-abelian Schutzenberger / projective matrix monoid lift `mu : Sigma* -> Mat_2(Z)`. -/
def wordLift : List DefectSym → Mat2Int
  | [] => Mat2Int.id
  | s :: rest => Mat2Int.mul (symMatrix s) (wordLift rest)

/-- Exact Monoid Homomorphism Theorem:
    `wordLift` maps concatenation of arbitrary-length defect words to `2 x 2` matrix product. -/
theorem wordLift_append :
    ∀ u v : List DefectSym, wordLift (u ++ v) = Mat2Int.mul (wordLift u) (wordLift v)
  | [], v => by
      simp [wordLift, Mat2Int.id_mul]
  | s :: u, v => by
      simp only [List.cons_append, wordLift]
      rw [wordLift_append u v, Mat2Int.mul_assoc]

/-- Non-commutativity of `[mu(T), mu(D)] != 0`. -/
theorem matT_matD_noncommuting :
    Mat2Int.mul (symMatrix .T) (symMatrix .D) ≠
      Mat2Int.mul (symMatrix .D) (symMatrix .T) := by
  decide

def wordT4D2 : List DefectSym := [.T, .T, .T, .T, .D, .D]
def wordD2T4 : List DefectSym := [.D, .D, .T, .T, .T, .T]

/-- Abelian Shadow Blindness vs. Non-Abelian Matrix Separation (`Probe 1` Certificate):
    `T^4 D^2` and `D^2 T^4` have identical Parikh vectors `(4, 2)` yet map to distinct
    `2 x 2` matrices `[[289, 211], [0, 16]]` and `[[289, 1303], [0, 16]]`. -/
theorem abelian_parikh_blind_but_matrix_separates :
    parikhCount wordT4D2 = (4, 2) ∧
      parikhCount wordD2T4 = (4, 2) ∧
      wordLift wordT4D2 = ⟨289, 211, 0, 16⟩ ∧
      wordLift wordD2T4 = ⟨289, 1303, 0, 16⟩ ∧
      wordLift wordT4D2 ≠ wordLift wordD2T4 := by
  decide

/-! ## 3. Positive Upper-Triangular Matrix Cone & Context-Free Rewrite Monotonicity -/

/-- Strictly-positive-diagonal upper-triangular matrix cone `K_+`. -/
def InUpperPosCone (M : Mat2Int) : Prop :=
  1 ≤ M.m00 ∧ 0 ≤ M.m01 ∧ M.m10 = 0 ∧ 1 ≤ M.m11

/-- Strict upper-right advancement cone `Delta_>` for local rewrites `u -> v`. -/
def StrictUpperAdvance (U V : Mat2Int) : Prop :=
  U.m10 = 0 ∧ V.m10 = 0 ∧
    U.m00 ≤ V.m00 ∧ U.m01 + 1 ≤ V.m01 ∧ U.m11 ≤ V.m11

theorem upperPosCone_id : InUpperPosCone Mat2Int.id := by
  unfold InUpperPosCone Mat2Int.id
  dsimp
  exact ⟨by omega, by omega, rfl, by omega⟩

theorem upperPosCone_mul {A B : Mat2Int}
    (hA : InUpperPosCone A) (hB : InUpperPosCone B) :
    InUpperPosCone (Mat2Int.mul A B) := by
  rcases hA with ⟨ha00, ha01, ha10, ha11⟩
  rcases hB with ⟨hb00, hb01, hb10, hb11⟩
  unfold InUpperPosCone Mat2Int.mul
  dsimp
  rw [ha10, hb10]
  simp only [Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]
  have hp00 : 1 ≤ A.m00 * B.m00 := by
    have h1 : 1 * 1 ≤ A.m00 * B.m00 :=
      Int.mul_le_mul ha00 hb00 (by omega) (by omega)
    omega
  have hp11 : 1 ≤ A.m11 * B.m11 := by
    have h1 : 1 * 1 ≤ A.m11 * B.m11 :=
      Int.mul_le_mul ha11 hb11 (by omega) (by omega)
    omega
  have hp01a : 0 ≤ A.m00 * B.m01 :=
    Int.mul_nonneg (by omega) hb01
  have hp01b : 0 ≤ A.m01 * B.m11 :=
    Int.mul_nonneg ha01 (by omega)
  exact ⟨hp00, by omega, trivial, hp11⟩

/-- Every multi-defect word `w ∈ {T, D}*` of arbitrary length/arity lies in `InUpperPosCone`. -/
theorem wordLift_in_upperPosCone :
    ∀ w : List DefectSym, InUpperPosCone (wordLift w)
  | [] => upperPosCone_id
  | s :: rest => by
      have ih := wordLift_in_upperPosCone rest
      have hs : InUpperPosCone (symMatrix s) := by
        cases s <;> unfold symMatrix InUpperPosCone <;> dsimp <;>
          exact ⟨by omega, by omega, rfl, by omega⟩
      exact upperPosCone_mul hs ih

/-- Universal Context-Independent Non-Abelian Matrix CTL* Theorem:
    If a local head rewrite `u -> v` satisfies `StrictUpperAdvance (wordLift u) (wordLift v)`,
    then for EVERY left prefix `p` and EVERY right suffix `s` in `{T, D}*` (with unbounded
    non-commuting defect count `r -> infinity`), rewriting `p ++ u ++ s -> p ++ v ++ s`
    strictly increases `(wordLift ...).m01` by at least `+1`! -/
theorem wordLift_context_rewrite_monotone
    (p u v s : List DefectSym)
    (hAdv : StrictUpperAdvance (wordLift u) (wordLift v)) :
    (wordLift (p ++ u ++ s)).m01 + 1 ≤ (wordLift (p ++ v ++ s)).m01 := by
  have hP : InUpperPosCone (wordLift p) := wordLift_in_upperPosCone p
  have hS : InUpperPosCone (wordLift s) := wordLift_in_upperPosCone s
  have hU : InUpperPosCone (wordLift u) := wordLift_in_upperPosCone u
  have hV : InUpperPosCone (wordLift v) := wordLift_in_upperPosCone v
  rcases hP with ⟨hp00, hp01, hp10, hp11⟩
  rcases hS with ⟨hs00, hs01, hs10, hs11⟩
  rcases hU with ⟨_, hu01, hu10, _⟩
  rcases hV with ⟨_, _, hv10, _⟩
  rcases hAdv with ⟨_, _, huv00, huv01, huv11⟩
  have hEqU : p ++ u ++ s = p ++ (u ++ s) := by simp [List.append_assoc]
  have hEqV : p ++ v ++ s = p ++ (v ++ s) := by simp [List.append_assoc]
  rw [hEqU, hEqV, wordLift_append p (u ++ s), wordLift_append u s,
      wordLift_append p (v ++ s), wordLift_append v s]
  unfold Mat2Int.mul
  dsimp
  rw [hu10, hv10]
  simp only [Int.zero_mul, Int.zero_add]
  -- Upper-right entry simplifies to:
  -- P00 * (U00 * S01 + U01 * S11) + P01 * (U11 * S11)
  have hTerm1 : (wordLift u).m00 * (wordLift s).m01 ≤ (wordLift v).m00 * (wordLift s).m01 :=
    Int.mul_le_mul_of_nonneg_right huv00 hs01
  have hTerm2 : ((wordLift u).m01 + 1) * (wordLift s).m11 ≤ (wordLift v).m01 * (wordLift s).m11 :=
    Int.mul_le_mul_of_nonneg_right huv01 (by omega)
  have hTerm2' : (wordLift u).m01 * (wordLift s).m11 + 1 ≤ (wordLift v).m01 * (wordLift s).m11 := by
    rw [Int.add_mul, Int.one_mul] at hTerm2
    omega
  have hMid :
      ((wordLift u).m00 * (wordLift s).m01 + (wordLift u).m01 * (wordLift s).m11) + 1 ≤
        (wordLift v).m00 * (wordLift s).m01 + (wordLift v).m01 * (wordLift s).m11 := by
    omega
  have hLeftScale :
      (wordLift p).m00 *
          (((wordLift u).m00 * (wordLift s).m01 + (wordLift u).m01 * (wordLift s).m11) + 1) ≤
        (wordLift p).m00 *
          ((wordLift v).m00 * (wordLift s).m01 + (wordLift v).m01 * (wordLift s).m11) :=
    Int.mul_le_mul_of_nonneg_left hMid (by omega)
  have hLeftExpand :
      (wordLift p).m00 *
          ((wordLift u).m00 * (wordLift s).m01 + (wordLift u).m01 * (wordLift s).m11) + 1 ≤
        (wordLift p).m00 *
          (((wordLift u).m00 * (wordLift s).m01 + (wordLift u).m01 * (wordLift s).m11) + 1) := by
    rw [Int.mul_add (wordLift p).m00 _ 1, Int.mul_one]
    omega
  have hRightTerm :
      (wordLift p).m01 * ((wordLift u).m11 * (wordLift s).m11) ≤
        (wordLift p).m01 * ((wordLift v).m11 * (wordLift s).m11) := by
    have hU11S11 : (wordLift u).m11 * (wordLift s).m11 ≤ (wordLift v).m11 * (wordLift s).m11 :=
      Int.mul_le_mul_of_nonneg_right huv11 (by omega)
    exact Int.mul_le_mul_of_nonneg_left hU11S11 hp01
  omega

/-! ## 4. Concrete Unbounded Multi-Defect Machine Certified Immortal via Matrix Lift -/

/-- State of an unbounded-arity multi-defect cascade machine:
    `leftPrefix` and `rightSuffix` carry arbitrarily many non-commuting `T` and `D` blocks.
    Halts iff `leftPrefix = [] ∧ rightSuffix = []`; otherwise condenses/splits defects
    locally (`D -> D T` or `T -> D` or boundary reflection), advancing `wordLift.m01`. -/
structure MultiDefectState where
  leftPrefix : List DefectSym
  rightSuffix : List DefectSym
  deriving DecidableEq, Repr

def fullWord (st : MultiDefectState) : List DefectSym :=
  st.leftPrefix ++ st.rightSuffix

def stepMultiDefect (st : MultiDefectState) : Option MultiDefectState :=
  match st.rightSuffix with
  | [] =>
      match st.leftPrefix with
      | [] => none
      | x :: xs => some ⟨[], (x :: xs) ++ [.T]⟩
  | .T :: rest => some ⟨st.leftPrefix ++ [.T, .T], rest⟩
  | .D :: rest => some ⟨st.leftPrefix ++ [.D], .T :: rest⟩

def InvMultiDefect (st : MultiDefectState) : Prop :=
  1 ≤ (wordLift (fullWord st)).m01

def matrixEnergyM01 (st : MultiDefectState) : Int :=
  (wordLift (fullWord st)).m01

theorem stepMultiDefect_strict_matrix_drift (st st' : MultiDefectState)
    (_hInv : InvMultiDefect st) (hStep : stepMultiDefect st = some st') :
    matrixEnergyM01 st + 1 ≤ matrixEnergyM01 st' := by
  unfold stepMultiDefect at hStep
  cases hR : st.rightSuffix with
  | nil =>
      rw [hR] at hStep
      cases hL : st.leftPrefix with
      | nil =>
          rw [hL] at hStep
          contradiction
      | cons x xs =>
          rw [hL] at hStep
          injection hStep with hEq
          subst hEq
          unfold matrixEnergyM01 fullWord
          simp only [hL, hR, List.append_nil, List.nil_append]
          have hAdv : StrictUpperAdvance (wordLift []) (wordLift [.T]) := by
            unfold StrictUpperAdvance; decide
          have hMono := wordLift_context_rewrite_monotone (x :: xs) [] [.T] [] hAdv
          simpa using hMono
  | cons sym rest =>
      rw [hR] at hStep
      cases sym with
      | T =>
          injection hStep with hEq
          subst hEq
          unfold matrixEnergyM01 fullWord
          simp only [hR]
          have hAdv : StrictUpperAdvance (wordLift [.T]) (wordLift [.T, .T]) := by
            unfold StrictUpperAdvance; decide
          have hMono := wordLift_context_rewrite_monotone st.leftPrefix [.T] [.T, .T] rest hAdv
          have hL1 : st.leftPrefix ++ [.T] ++ rest = st.leftPrefix ++ (.T :: rest) := by
            simp [List.append_assoc]
          have hL2 : st.leftPrefix ++ [.T, .T] ++ rest = (st.leftPrefix ++ [.T, .T]) ++ rest := rfl
          rw [hL1, hL2] at hMono
          exact hMono
      | D =>
          injection hStep with hEq
          subst hEq
          unfold matrixEnergyM01 fullWord
          simp only [hR]
          have hAdv : StrictUpperAdvance (wordLift [.D]) (wordLift [.D, .T]) := by
            unfold StrictUpperAdvance; decide
          have hMono := wordLift_context_rewrite_monotone st.leftPrefix [.D] [.D, .T] rest hAdv
          have hL1 : st.leftPrefix ++ [.D] ++ rest = st.leftPrefix ++ (.D :: rest) := by
            simp [List.append_assoc]
          have hL2 : st.leftPrefix ++ [.D, .T] ++ rest = (st.leftPrefix ++ [.D]) ++ (.T :: rest) := by
            simp [List.append_assoc]
          rw [hL1, hL2] at hMono
          exact hMono

theorem invMultiDefect_preserved : IsInvariant stepMultiDefect InvMultiDefect := by
  intro st st' hInv hStep
  have hDrift := stepMultiDefect_strict_matrix_drift st st' hInv hStep
  unfold InvMultiDefect matrixEnergyM01 at *
  omega

theorem invMultiDefect_safe (st : MultiDefectState) (hInv : InvMultiDefect st) :
    stepMultiDefect st ≠ none := by
  intro hNone
  unfold stepMultiDefect at hNone
  cases hR : st.rightSuffix with
  | cons s rs =>
      rw [hR] at hNone
      cases s <;> simp at hNone
  | nil =>
      rw [hR] at hNone
      cases hL : st.leftPrefix with
      | cons x xs =>
          rw [hL] at hNone
          simp at hNone
      | nil =>
          unfold InvMultiDefect fullWord at hInv
          rw [hL, hR] at hInv
          simp [wordLift, Mat2Int.id] at hInv

/-- Unconditional Immortality Theorem for Arbitrary-Arity Multi-Defect Cascades:
    Starting from `[D]` (`⟨[], [.D]⟩`), `stepMultiDefect` never halts AND visits
    infinitely many distinct unbounded-defect states (`IsImmortalOrbit`). -/
theorem multiDefect_cascade_immortal :
    IsImmortalOrbit stepMultiDefect ⟨[], [.D]⟩ := by
  have hInit : InvMultiDefect ⟨[], [.D]⟩ := by
    unfold InvMultiDefect; decide
  exact immortal_of_safe_invariant_and_drift
    stepMultiDefect InvMultiDefect matrixEnergyM01 1 (by omega)
    invMultiDefect_preserved invMultiDefect_safe stepMultiDefect_strict_matrix_drift
    ⟨[], [.D]⟩ hInit

end CryptidSolvePhase4
