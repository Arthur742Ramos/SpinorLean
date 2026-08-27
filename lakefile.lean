import Lake
open Lake DSL

package «spinor-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "f23306121184717ace04f3ac514be974e3224c8b"

@[default_target]
lean_lib «Spinor» where

lean_lib «Challenge» where
  roots := #[`Challenge]

lean_lib «Solution» where
  roots := #[`Solution]
