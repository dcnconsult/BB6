/-
  CryptidSolve.Tactic
  ===================
  Reusable core Lean 4 proof automation macros (`cryptid_step_round`, `cryptid_step_omega`)
  for discharging piecewise-affine invariant preservation and Lyapunov drift goals
  across nested parity/inequality branch tables.

  Pipeline correspondence:
    - Stage 1 (Modular / Sector Pruning): `cryptid_step_omega` proves forward
      closure `P x → step x = some x' → P x'` and dead-branch disjointness.
    - Stage 3a / 3b (Global Lyapunov Aperiodicity): `cryptid_step_omega` proves
      `E x + d ≤ E x'` or `LexProgress E rank x x'` across all surviving branches.
-/

import CryptidSolve.Basic

namespace CryptidSolve

/-- Single breadth-first round of branch resolution:
    - Immediately closes `none = some s'` leaves via `contradiction`;
    - Immediately closes `some expr = some s'` leaves via `injection` + `dsimp` + `omega`
      (preventing redundant `whnf` scans on already-split leaves);
    - Splits one outer `if`/`match` layer on remaining composite branches. -/
macro "cryptid_step_round " hStep:ident : tactic =>
  `(tactic| all_goals (
      first
      | contradiction
      | (injection $hStep:ident with hEq
         subst hEq
         dsimp only [] at *
         all_goals (try split)
         all_goals (try split)
         all_goals (try split)
         all_goals (try split)
         all_goals (try split)
         all_goals (try split)
         all_goals omega)
      | split at $hStep:ident
    ))

/-- Core branch-splitting linear/modular arithmetic discharger (`s'` a free variable):
    Executes up to 14 breadth-first rounds of `cryptid_step_round` (once all leaves
    close, remaining rounds on 0 goals are instantaneous no-ops). -/
macro "cryptid_step_omega" hStep:ident : tactic =>
  `(tactic| (
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
      cryptid_step_round $hStep:ident
  ))

end CryptidSolve
