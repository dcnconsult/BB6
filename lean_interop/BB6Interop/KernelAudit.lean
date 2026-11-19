import Lean
import BB6Interop

/-! Fail closed on every transitive axiom of an adapter theorem. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc name info =>
    if (Name.mkSimple "BB6Interop").isPrefixOf name then acc.push (name, info) else acc
  let mut count := 0
  let mut footprint : Array Name := #[]
  for (name, info) in entries do
    match info with
    | .axiomInfo _ => throwError s!"INTEROP AUDIT FAIL: custom axiom {name}"
    | .thmInfo _ =>
      let axs ← collectAxioms name
      for ax in axs do
        unless (#[Name.mkSimple "propext", Name.str (Name.mkSimple "Quot") "sound",
            Name.str (Name.mkSimple "Classical") "choice"]).contains ax do
          throwError s!"INTEROP AUDIT FAIL: {name} depends on non-allowlisted axiom {ax}"
        unless footprint.contains ax do footprint := footprint.push ax
      unless name.isInternal do
        count := count + 1
        IO.println s!"AXIOMS {name}: {axs.toList}"
    | _ => pure ()
  IO.println s!"INTEROP AUDIT PASS: {count} non-internal theorem constants; axioms {footprint.toList}"

#print axioms BB6Interop.AppC7.gate_unreachable
#print axioms BB6Interop.AppC7.sweep_gate_unreachable
#print axioms BB6Interop.AppC8.clean_exact_time
#print axioms BB6Interop.AppC8.blank_clean_applied
