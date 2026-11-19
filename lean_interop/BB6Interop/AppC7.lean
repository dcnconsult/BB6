import BB6Interop.Zipper
import CryptidSolvePhase4.AppC7RawGate
import BusyBeaver.BB6.NonHalt.M_1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC

namespace BB6Interop.AppC7
open CryptidSolvePhase4
namespace Raw
export CryptidSolvePhase4.AppC7Raw (State Cfg delta step run initial gateCfg HaltsAfter)
end Raw

abbrev machine := BusyBeaver.M_1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC.target

def index : Raw.State → Fin 6
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def pack (c : Raw.Cfg) : Zipper Raw.State := ⟨c.st,c.left,c.right⟩
def encode (c : Raw.Cfg) := BB6Interop.encode index (pack c)

theorem table_agrees (s : Raw.State) (b : Bool) :
    machine (index s) (bit b) = (Raw.delta s b).map (instruction index) := by
  cases s <;> cases b <;> rfl

theorem pack_step (c : Raw.Cfg) :
    zipperStep Raw.delta (pack c) = (Raw.step c).map pack := by
  rcases c with ⟨s,l,r⟩
  cases s <;> cases r with
  | nil => cases l <;> rfl
  | cons b r => cases b <;> cases l <;> rfl

theorem step_commutes (c : Raw.Cfg) :
    BusyBeaver.step machine (encode c) = (Raw.step c).map encode := by
  rw [encode, encode_step index Raw.delta machine table_agrees, pack_step, Option.map_map]
  rfl

theorem run_commutes (n : Nat) (c : Raw.Cfg) :
    BusyBeaver.multiStep machine (encode c) n = (Raw.run n c).map encode :=
  transfer_run Raw.step Raw.run (fun _ => rfl) (fun _ _ => rfl)
    machine encode step_commutes n c

theorem blank_agrees :
    encode ⟨.A,[],[]⟩ = BusyBeaver.init [] := rfl

/-- Explicit dependence on the pinned upstream non-halting certificate. -/
theorem blank_nonhalting : BusyBeaver.IsNotHalt machine :=
  BusyBeaver.M_1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC.is_not_halt

theorem gate_exact_time (b : Nat) :
    (∀ t, t < 16*b*b+28*b+15 →
      ∃ c, BusyBeaver.ReachesIn machine t (encode (Raw.initial b)) c) ∧
    BusyBeaver.multiStep machine (encode (Raw.initial b)) (16*b*b+28*b+15) = none := by
  obtain ⟨definedPrefixes,halt⟩ := CryptidSolvePhase4.AppC7Raw.appC7_raw_gate_exact_time b
  constructor
  · intro t ht
    obtain ⟨c,hc⟩ := definedPrefixes t ht
    exact ⟨encode c, by rw [BusyBeaver.ReachesIn, run_commutes, hc]; rfl⟩
  · rw [run_commutes, halt]; rfl

theorem gate_unreachable (b : Nat) :
    ¬ BusyBeaver.ReachesStar machine (BusyBeaver.init []) (encode (Raw.initial b)) :=
  unreachable_of_halts Raw.step Raw.run machine encode step_commutes run_commutes
    blank_nonhalting (Raw.initial b) (16*b*b+28*b+14)
    (CryptidSolvePhase4.AppC7Raw.appC7_raw_gate_halts b)

theorem sweep_gate_unreachable (a r : Nat) :
    ¬ BusyBeaver.ReachesStar machine (BusyBeaver.init []) (encode (Raw.gateCfg a r)) :=
  unreachable_of_halts Raw.step Raw.run machine encode step_commutes run_commutes
    blank_nonhalting (Raw.gateCfg a r) (appC7GateSweep a r - 1)
    (CryptidSolvePhase4.AppC7Raw.gate_sweep r a)


/-- The same exclusion in the original finite-zipper execution model. -/
theorem gate_unreachable_local (b n : Nat) :
    Raw.run n ⟨.A,[],[]⟩ ≠ some (Raw.initial b) := by
  intro h
  apply gate_unreachable b
  refine ⟨n, ?_⟩
  rw [← blank_agrees, run_commutes, h]
  rfl

theorem sweep_gate_unreachable_local (a r n : Nat) :
    Raw.run n ⟨.A,[],[]⟩ ≠ some (Raw.gateCfg a r) := by
  intro h
  apply sweep_gate_unreachable a r
  refine ⟨n, ?_⟩
  rw [← blank_agrees, run_commutes, h]
  rfl

/-- The halting configuration itself is reached after T-1 defined transitions. -/
theorem gate_halts_after (b : Nat) :
    ∃ c, BusyBeaver.ReachesIn machine (16*b*b+28*b+14) (encode (Raw.initial b)) c ∧
      BusyBeaver.step machine c = none := by
  obtain ⟨c,hc,halt⟩ := CryptidSolvePhase4.AppC7Raw.appC7_raw_gate_halts b
  refine ⟨encode c, ?_, ?_⟩
  · rw [BusyBeaver.ReachesIn, run_commutes, hc]; rfl
  · rw [step_commutes, halt]; rfl

end BB6Interop.AppC7
