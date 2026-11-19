import BusyBeaver.Basic

/-! Finite zero-padded zipper to the pinned BusyBeaver semantics.
The map deliberately quotients redundant trailing zeros; no injectivity is assumed. -/
namespace BB6Interop
open Turing BusyBeaver

def bit (b : Bool) : Fin 2 := if b then 1 else 0

def read : List Bool → Bool
  | [] => false
  | b :: _ => b

def half : List Bool → ListBlank (Fin 2)
  | [] => default
  | b :: l => ListBlank.cons (bit b) (half l)

@[simp] theorem half_head (l : List Bool) : (half l).head = bit (read l) := by
  cases l <;> simp [half, read, bit] <;> rfl

@[simp] theorem half_tail (l : List Bool) : (half l).tail = half l.tail := by
  cases l <;> simp [half]

structure Zipper (S : Type) where
  st : S
  left : List Bool
  right : List Bool

def encode {S : Type} (index : S → Fin 6) (c : Zipper S) :
    BusyBeaver.Cfg (Fin 2) (Fin 6) :=
  BusyBeaver.Cfg.headRight (index c.st) (half c.left) (half c.right)

def zipperStep {S : Type} (delta : S → Bool → Option (Bool × Bool × S))
    (c : Zipper S) : Option (Zipper S) :=
  match delta c.st (read c.right) with
  | none => none
  | some (w, dir, st) =>
      if dir then some ⟨st, w :: c.left, c.right.tail⟩
      else some ⟨st, c.left.tail, read c.left :: w :: c.right.tail⟩

def instruction {S : Type} (index : S → Fin 6) (a : Bool × Bool × S) :
    Option (Fin 6) × BusyBeaver.Stmt (Fin 2) :=
  (some (index a.2.2), .write (bit a.1) (if a.2.1 then .right else .left))

/-- One-step commuting square, including an undefined instruction. -/
theorem encode_step {S : Type} (index : S → Fin 6)
    (delta : S → Bool → Option (Bool × Bool × S))
    (M : BusyBeaver.Machine (Fin 2) (Fin 6))
    (table : ∀ s b, M (index s) (bit b) = (delta s b).map (instruction index))
    (c : Zipper S) :
    BusyBeaver.step M (encode index c) =
      (zipperStep delta c).map (encode index) := by
  rcases c with ⟨s,l,r⟩
  simp only [encode, BusyBeaver.Cfg.headRight, BusyBeaver.step, half_head, table]
  cases h : delta s (read r) with
  | none => simp [zipperStep, h]
  | some a =>
    rcases a with ⟨w,dir,s'⟩
    cases dir <;>
      simp [zipperStep, h, instruction, encode, BusyBeaver.Cfg.headRight,
        Tape.write, Tape.move, half]

/-- Lift an arbitrary recursively defined local run, with exact time preserved. -/
theorem transfer_run {C : Type} (localStep : C → Option C)
    (run : Nat → C → Option C)
    (zero : ∀ c, run 0 c = some c)
    (succ : ∀ n c, run (n + 1) c = (localStep c).bind (run n))
    (M : BusyBeaver.Machine (Fin 2) (Fin 6))
    (φ : C → BusyBeaver.Cfg (Fin 2) (Fin 6))
    (commutes : ∀ c, BusyBeaver.step M (φ c) = (localStep c).map φ)
    (n : Nat) (c : C) :
    BusyBeaver.multiStep M (φ c) n = (run n c).map φ := by
  induction n generalizing c with
  | zero => simp [zero]
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ, commutes, succ]
    cases h : localStep c with
    | none => simp
    | some d => simpa [h] using ih d

/-- A reachable local halting witness contradicts upstream blank non-halting. -/
theorem unreachable_of_halts {C : Type}
    (localStep : C → Option C) (run : Nat → C → Option C)
    (M : BusyBeaver.Machine (Fin 2) (Fin 6))
    (φ : C → BusyBeaver.Cfg (Fin 2) (Fin 6))
    (step_eq : ∀ c, BusyBeaver.step M (φ c) = (localStep c).map φ)
    (run_eq : ∀ n c, BusyBeaver.multiStep M (φ c) n = (run n c).map φ)
    (nonhalt : BusyBeaver.IsNotHalt M)
    (c : C) (n : Nat) (halts : ∃ d, run n c = some d ∧ localStep d = none) :
    ¬ BusyBeaver.ReachesStar M (BusyBeaver.init []) (φ c) := by
  rintro reachable
  obtain ⟨d, hd, halt⟩ := halts
  have tail : BusyBeaver.ReachesStar M (φ c) (φ d) :=
    ⟨n, by rw [run_eq, hd]; rfl⟩
  have safe := nonhalt (φ d) (reachable.trans tail)
  rw [step_eq, halt] at safe
  contradiction

end BB6Interop
