/-
  CryptidSolvePhase4.KernelAudit
  ==============================
  Compile-time Lean 4 Kernel Axiom Auditor for the `CryptidSolvePhase4` library.
  Executed automatically during `lake build` to verify in the Lean 4 kernel environment:
    1. Zero custom `axiom` declarations exist in namespace `CryptidSolvePhase4`.
    2. Only propext, Quot.sound, and Classical.choice are allowed transitively.
       Zero theorems in `CryptidSolvePhase4` transitively depend on `sorryAx`.
    3. Reports total kernel-verified theorem count and core foundational footprint.
-/

import Lean
import CryptidSolvePhase4

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let entries : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name cinfo =>
      if (`CryptidSolvePhase4).isPrefixOf name then acc.push (name, cinfo) else acc
  let mut thmCount : Nat := 0
  let mut seenAxioms : Array Name := #[]
  for (name, cinfo) in entries do
    match cinfo with
    | .axiomInfo _ =>
        throwError s!"FATAL KERNEL AUDIT: Custom axioms entry '{name}' found in CryptidSolvePhase4!"
    | .thmInfo _ =>
        let axs ← collectAxioms name
        if axs.contains ``sorryAx then
          throwError s!"FATAL KERNEL AUDIT: Theorem '{name}' depends on sorryAx!"
        for ax in axs do
          if !(#[``propext, ``Quot.sound, ``Classical.choice]).contains ax then
            throwError s!"FATAL KERNEL AUDIT: Theorem '{name}' depends on non-allowlisted foundational constant '{ax}'!"
          if !seenAxioms.contains ax then
            seenAxioms := seenAxioms.push ax
        if !name.isInternal then
          thmCount := thmCount + 1
    | _ => pure ()
  IO.println s!"[PHASE-4 KERNEL AUDIT PASS] Verified {thmCount} CryptidSolvePhase4 theorems in Lean 4 kernel (0 sorryAx, 0 custom axioms). Core axioms used: {seenAxioms.toList}"
