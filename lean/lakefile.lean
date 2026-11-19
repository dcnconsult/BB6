import Lake
open Lake DSL

package «cryptid_solve» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «CryptidSolve» where
  roots := #[`CryptidSolve]

@[default_target]
lean_lib «KernelAudit» where
  roots := #[`CryptidSolve.KernelAudit]
