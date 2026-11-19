/-
  CryptidSolve.KernelAudit
  ========================
  Compile-time Lean 4 Kernel Axiom Auditor for the `CryptidSolve` library.
  Executed automatically during `lake build` to verify in the Lean 4 kernel environment:
    1. Zero custom `axiom` declarations exist in namespace `CryptidSolve`.
    2. Only propext, Quot.sound, and Classical.choice are allowed transitively.
       Zero theorems in `CryptidSolve` transitively depend on `sorryAx`.
    3. Reports total kernel-verified theorem count and core axiom footprint.
-/

import Lean
import CryptidSolve

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let entries : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name cinfo =>
      if (`CryptidSolve).isPrefixOf name then acc.push (name, cinfo) else acc
  let mut thmCount : Nat := 0
  let mut seenAxioms : Array Name := #[]
  for (name, cinfo) in entries do
    match cinfo with
    | .axiomInfo _ =>
        throwError s!"FATAL KERNEL AUDIT: Custom axioms entry '{name}' found in CryptidSolve!"
    | .thmInfo _ =>
        -- Skip compiler-generated internal equational/splitter helpers if desired,
        -- though auditing ALL `.thmInfo` constants in `CryptidSolve` is even stronger!
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
  IO.println s!"[KERNEL AUDIT PASS] Verified {thmCount} CryptidSolve theorems in Lean 4 kernel (0 sorryAx, 0 custom axioms). Core axioms used: {seenAxioms.toList}"
