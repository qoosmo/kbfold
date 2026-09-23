import Lake
open Lake DSL

package KBFold where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

@[default_target]
lean_lib KBFold where
