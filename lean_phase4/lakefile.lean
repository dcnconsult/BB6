import Lake
open Lake DSL

package «cryptid_solve_phase4» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «CryptidSolvePhase4» where
  roots := #[`CryptidSolvePhase4]

@[default_target]
lean_lib «Phase4KernelAudit» where
  roots := #[`CryptidSolvePhase4.KernelAudit]
