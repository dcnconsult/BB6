import BB6Interop.Zipper
import BusyBeaver.Bridge
import CryptidSolvePhase4.AppC8RawMod2Sector

namespace BB6Interop.AppC8
open CryptidSolvePhase4
namespace Raw
export CryptidSolvePhase4.AppC8Raw
  (State Cfg delta step run shuttleCfg cleanCfg blankCfg shuttleTailCfg defectTail)
end Raw

/-- Exact table absent from the inspected upstream machine-named catalog. -/
def rawMachine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LAHHH"
abbrev machine := rawMachine.toBB

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

theorem blank_agrees : encode Raw.blankCfg = BusyBeaver.init [] := rfl

/-- All successful local exact-time theorems transfer, not only the named examples below. -/
theorem reaches_in {n : Nat} {c d : Raw.Cfg} (h : Raw.run n c = some d) :
    BusyBeaver.ReachesIn machine n (encode c) (encode d) := by
  rw [BusyBeaver.ReachesIn, run_commutes, h]
  rfl

theorem blank_reaches_in {n : Nat} {d : Raw.Cfg} (h : Raw.run n Raw.blankCfg = some d) :
    BusyBeaver.ReachesIn machine n (BusyBeaver.init []) (encode d) := by
  rw [← blank_agrees]
  exact reaches_in h

theorem shuttle_exact_time (k m : Nat) (hm : m ≥ 5) :
    BusyBeaver.ReachesIn machine (12*k+26)
      (encode (Raw.shuttleCfg k m)) (encode (Raw.shuttleCfg (k+2) (m-4))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_raw_shuttle k m hm)

theorem rounds_exact_time (r k m : Nat) (hm : m ≥ 4*r+1) :
    BusyBeaver.ReachesIn machine (12*r*k+12*r*(r-1)+26*r)
      (encode (Raw.shuttleCfg k m)) (encode (Raw.shuttleCfg (k+2*r) (m-4*r))) :=
  by simpa [Nat.mul_assoc] using reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_raw_rounds_closed_form r k m hm)

theorem reset_exact_time (n : Nat) :
    BusyBeaver.ReachesIn machine (5*(n+1)+43)
      (encode (Raw.cleanCfg (n+1))) (encode (Raw.shuttleCfg 3 (3*(n+1)-2))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_raw_reset n)

theorem exit_exact_time (k : Nat) :
    BusyBeaver.ReachesIn machine (3*k+6)
      (encode (Raw.shuttleCfg k 2)) (encode (Raw.cleanCfg (k+1))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_raw_exit k)

theorem clean_exact_time (q : Nat) :
    BusyBeaver.ReachesIn machine (108*q*q+332*q+238)
      (encode (Raw.cleanCfg (4*(q+1)))) (encode (Raw.cleanCfg (6*q+8))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_clean_macro_raw q)

theorem odd_exact_time (a : Nat) :
    BusyBeaver.ReachesIn machine (108*a*a+398*a+356)
      (encode (Raw.shuttleCfg (4*a+3) 3)) (encode (Raw.shuttleCfg 0 (18*a+31))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_odd_excursion_closed a)

theorem mod2_exact_time (a : Nat) :
    BusyBeaver.ReachesIn machine (108*a*a+398*a+388)
      (encode (Raw.shuttleCfg (4*a+2) 3))
      (encode (Raw.shuttleTailCfg 0 (18*a+19) (Raw.defectTail 8))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_mod2_reduction_closed a)

theorem mod16_exact_time (b : Nat) :
    BusyBeaver.ReachesIn machine (14364*b*b+18656*b+6552)
      (encode (Raw.shuttleCfg (16*b+6) 3)) (encode (Raw.cleanCfg (54*b+37))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_mod16_carry b)

theorem mod1_exact_time (a : Nat) :
    BusyBeaver.ReachesIn machine (108*a*a+260*a+147)
      (encode (Raw.shuttleCfg (4*a+1) 3)) (encode (Raw.cleanCfg (6*a+6))) :=
  reaches_in (CryptidSolvePhase4.AppC8Raw.appC8_mod1_carry a)

theorem blank_clean_entry :
    BusyBeaver.ReachesIn machine 2600695 (BusyBeaver.init []) (encode (Raw.cleanCfg 696)) :=
  blank_reaches_in CryptidSolvePhase4.AppC8Raw.appC8_blank_clean_entry

theorem blank_clean_applied :
    BusyBeaver.ReachesIn machine 5890701 (BusyBeaver.init []) (encode (Raw.cleanCfg 1046)) :=
  blank_reaches_in CryptidSolvePhase4.AppC8Raw.appC8_blank_clean_macro_applied

theorem blank_prefix_defined (j : Nat) (hj : j ≤ 5890701) :
    ∃ c, BusyBeaver.ReachesIn machine j (BusyBeaver.init []) c := by
  obtain ⟨c,hc⟩ := CryptidSolvePhase4.AppC8Raw.appC8_blank_prefix_5890701 j hj
  exact ⟨encode c, blank_reaches_in hc⟩

end BB6Interop.AppC8
