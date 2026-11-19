import BB6Interop.AppC8RunLists

/-! Finite rejection traces, checked entirely by the Lean kernel. -/
namespace BB6Interop.AppC8ResidualTape
open CryptidSolvePhase4.AppC8Raw BB6Interop.AppC8Continuation BB6Interop.AppC8RunLists

def boundaryHead (c : Cfg) : Bool := decide (c.st = .A) && c.left.all Bool.not

theorem boundary_head_true {c : Cfg} (hc : Boundary c) : boundaryHead c = true := by
  rcases hc with ⟨w, hw, rfl⟩
  rfl

def rejectTrace : List Cfg → Bool
  | [] => false
  | [c] => Bool.not (boundaryHead c) && (step c).isNone
  | c :: d :: cs => Bool.not (boundaryHead c) && (decide (step c = some d) && rejectTrace (d :: cs))

theorem head_false {c : Cfg} (h : Bool.not (boundaryHead c) = true) : boundaryHead c = false := by
  cases hc : boundaryHead c with
  | false => rfl
  | true => simp [hc] at h

theorem reject_trace_sound {cs : List Cfg} {c : Cfg} (h : rejectTrace (c :: cs) = true) :
    ∀ t d, run t c = some d → ¬ Boundary d := by
  induction cs generalizing c with
  | nil =>
      have parts : (Bool.not (boundaryHead c) = true) ∧ (step c).isNone = true := by
        simpa only [rejectTrace, Bool.and_eq_true] using h
      have hh := head_false parts.1
      have hs : step c = none := by
        cases he : step c <;> simp_all
      intro t d hr hb
      cases t with
      | zero =>
          have eq : c = d := Option.some.inj hr
          subst d
          rw [boundary_head_true hb] at hh
          contradiction
      | succ t => simp [run, hs] at hr
  | cons e cs ih =>
      have parts : (Bool.not (boundaryHead c) = true) ∧ step c = some e ∧ rejectTrace (e :: cs) = true := by
        simpa only [rejectTrace, Bool.and_eq_true, decide_eq_true_eq] using h
      intro t d hr hb
      cases t with
      | zero =>
          have hh := head_false parts.1
          have eq : c = d := Option.some.inj hr
          subst d
          rw [boundary_head_true hb] at hh
          contradiction
      | succ t =>
          exact ih parts.2.2 t d (by simpa [run, parts.2.1] using hr) hb

theorem no_progress_of_trace {c : Cfg} {cs : List Cfg} (h : rejectTrace (c :: cs) = true) :
    ¬ Progress c := by
  rintro ⟨t, d, ht, hr, hb⟩
  exact reject_trace_sound h t d hr hb


/-- A checked trace also gives its exact last defined configuration and next halt. -/
theorem reject_trace_steps {cs : List Cfg} {c : Cfg} (h : rejectTrace (c :: cs) = true) :
    (∃ d, run cs.length c = some d) ∧ run (cs.length+1) c = none := by
  induction cs generalizing c with
  | nil =>
      have parts : (Bool.not (boundaryHead c) = true) ∧ (step c).isNone = true := by
        simpa only [rejectTrace, Bool.and_eq_true] using h
      have hs : step c = none := by cases he : step c <;> simp_all
      exact ⟨⟨c, rfl⟩, by simp [run, hs]⟩
  | cons e cs ih =>
      have parts : (Bool.not (boundaryHead c) = true) ∧
          step c = some e ∧ rejectTrace (e :: cs) = true := by
        simpa only [rejectTrace, Bool.and_eq_true, decide_eq_true_eq] using h
      obtain ⟨⟨d, hd⟩, hh⟩ := ih parts.2.2
      constructor
      · refine ⟨d, ?_⟩
        change run (cs.length+1) c = some d
        rw [run, parts.2.1]
        exact hd
      · change run ((cs.length+1)+1) c = none
        rw [run, parts.2.1]
        exact hh

/-- Little-endian finite tape data; lengths preserve explicit zero padding. -/
def traceBits : Nat → Nat → List Bool
  | 0, _ => []
  | n+1, v => (v % 2 == 1) :: traceBits n (v / 2)

def traceCfg (s : State) (ln lv rn rv : Nat) : Cfg :=
  ⟨s, traceBits ln lv, traceBits rn rv⟩

end BB6Interop.AppC8ResidualTape
