/-
  # SpinorLean Mathlib inventory

  The current Mathlib snapshot already provides:

  * `CliffordAlgebra Q`, the canonical map `CliffordAlgebra.ι Q`,
    and the universal property `CliffordAlgebra.lift`.
  * `CliffordAlgebra.contractLeft`, `contractRight`, `changeForm`,
    and the linear equivalence `CliffordAlgebra.equivExterior`.
  * `pinGroup Q`, `spinGroup Q`, the even subalgebra,
    and the basic conjugation action facts used to connect Clifford and spin data.
  * `ExteriorAlgebra R M` together with the fixed-degree submodules `⋀[R]^n M`.
  * `QuadraticMap.radical`, `QuadraticMap.IsOrtho`, `QuadraticMap.Anisotropic`,
    and finite-dimensional signature/diagonalization tools.

  The main gaps for this project are the missing API for totally isotropic subspaces,
  Witt-index bookkeeping, and a project-level spinor-module construction.
-/

import Spinor.Notation

/-!
# Mathlib inventory for SpinorLean

Documentation-only module recording the Mathlib APIs this project builds on and the gaps it
sets out to fill. The `Spinor` namespace here is intentionally empty; see the file header
comment above for the current inventory.

The main gaps targeted elsewhere in this library are an API for totally isotropic subspaces
(`Spinor.Isotropic`), Witt-index bookkeeping (`Spinor.WittDecomp`), and a project-level
spinor-module construction with its Clifford and spin-group actions
(`Spinor.Basic`, `Spinor.ExteriorModel`, `Spinor.CliffordAction`, `Spinor.SpinRep`,
`Spinor.Presentation`).
-/

namespace Spinor

end Spinor
