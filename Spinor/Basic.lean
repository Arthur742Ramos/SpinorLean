/-
  Core spinor-module definitions.
-/

import Spinor.WittDecomp

/-!
# Core spinor-module definition

Top-level spinor-module alias used by the ambient exterior-algebra model. The current
implementation takes `SpinorModule Q` to be `ExteriorAlgebra R M` transported along
`CliffordAlgebra.equivExterior`, which yields a faithful Clifford action out of the box.
The more refined chosen-subspace `⋀W` model lives in `Spinor.ExteriorModel` and is packaged
through the presentation API in `Spinor.Presentation`.

## Main declarations

* `Spinor.SpinorModule` — the ambient `ExteriorAlgebra R M` viewed as a `CliffordAlgebra Q`
  module via `Spinor.CliffordAction`.
-/

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/--
The current `SpinorModule` implementation uses the exterior-algebra model coming from
`CliffordAlgebra.equivExterior`.

This gives a faithful Clifford action immediately. The more refined construction via a maximal
totally isotropic subspace remains future work at the global `SpinorModule` level; see
`Spinor.Presentation` for the packaged chosen-model API attached either to an explicit hyperbolic
presentation `Q ≃ dualProd K W`, to split data consisting of a half-dimensional totally isotropic
subspace plus a chosen complement via `HyperbolicPresentation.ofIsCompl`, or, more specifically,
to an explicit Witt presentation `Q ≃ dualProd K Q.wittSubspace`; in split rank, the canonical
Witt model can also choose its complement internally via `splitWittPresentation`. At the lower
linear-algebra level, `Spinor.WittDecomp` now also provides the general linear Witt decomposition
`QuadraticForm.wittLinearDecomposition : V ≃ Q.wittSubspace × Q.wittSubspace* × V₀` together with
the residual factor `QuadraticForm.wittResidualSubspace`, as well as the corresponding general
quadratic-form splitting `QuadraticForm.wittIsometryEquiv :
  Q ≃ dualProd K Q.wittSubspace ⊕ Q₀`. That general splitting is also packaged in
`Spinor.WittPresentation`, with the hyperbolic factor exposed as
`HyperbolicPresentation.canonicalWittFactor`. Accordingly, the parity pieces in `Spinor.Chiral`
belong to this ambient regular model, while the actual chosen-model half-spin modules live in
`Spinor.Presentation`.
-/
abbrev SpinorModule (_Q : QuadraticForm R M) := ExteriorAlgebra R M

end Spinor
