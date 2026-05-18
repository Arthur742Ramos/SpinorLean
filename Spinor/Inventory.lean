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

  The initial gaps for this project were the missing API for totally isotropic subspaces,
  Witt-index bookkeeping, and a project-level spinor-module construction.  The project modules
  below supply the companion APIs used by the paper.
-/

import Spinor.Notation

/-!
# Mathlib inventory for SpinorLean

Documentation-only module recording the Mathlib APIs this project builds on and the companion
APIs it adds around them. The `Spinor` namespace here is intentionally empty; see the file header
comment above for the current inventory.

The main project-level additions are an API for totally isotropic subspaces
(`Spinor.Isotropic`), Witt-index bookkeeping (`Spinor.WittDecomp`), and a chosen-model
spinor-module construction with its Clifford, spin-group, half-spin, and image-subgroup
projective-descent actions (`Spinor.Basic`, `Spinor.ExteriorModel`,
`Spinor.CliffordAction`, `Spinor.SpinRep`, `Spinor.Chiral`, `Spinor.Presentation`).
-/

namespace Spinor

end Spinor
