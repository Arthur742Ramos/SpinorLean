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

namespace Spinor

end Spinor
