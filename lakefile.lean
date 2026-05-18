import Lake
open Lake DSL

package «spinor-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "11873348d8bf19440253d9282cc4e9423432e5ea"

@[default_target]
lean_lib «Spinor» where
