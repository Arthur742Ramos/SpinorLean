/-
  Core spinor-module definitions.
-/

import Spinor.WittDecomp

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
`HyperbolicPresentation.canonicalWittFactor`.
-/
abbrev SpinorModule (_Q : QuadraticForm R M) := ExteriorAlgebra R M

end Spinor
