# SpinorLean

First-ever formalization of spinor representations from Clifford algebras in Lean 4 / Mathlib.

## What This Is

The **spinor representation** is one of the most important constructions in mathematics and physics — it's how the Spin group acts on "square roots of geometry." Despite Clifford algebras and Spin groups already existing in Mathlib, nobody has formalized the actual spinor module that connects them.

This project fills that gap.

## Structure

```
SpinorLean/
├── Spinor.lean
├── Spinor/
│   ├── Mathlib.lean        -- Shared Mathlib imports
│   ├── Notation.lean       -- Project conventions and abbreviations
│   ├── Inventory.lean      -- Mathlib audit and documented gaps
│   ├── Isotropic.lean      -- Totally isotropic subspaces
│   ├── WittDecomp.lean     -- Witt index and maximal isotropic existence
│   ├── Basic.lean          -- Exterior-model spinor module alias
│   ├── ExteriorModel.lean  -- Chosen `⋀W` models, dimensions, wedge/contraction operators
│   ├── HyperbolicAction.lean -- Transport of the chosen model along explicit split isometries
│   ├── Presentation.lean   -- First-class explicit hyperbolic presentations and their chosen models
│   ├── ProdNeg.lean        -- Canonical split presentation and chosen model for `Q ⊕ (-Q)`
│   ├── CliffordAction.lean -- Transported Clifford action on the exterior model
│   ├── SpinRep.lean        -- Restriction of the action to `spinGroup`
│   └── Chiral.lean         -- Transported chiral decomposition and spin invariance
├── ROADMAP.md
├── AGENTS.md
└── lakefile.lean
```

## Building

```bash
lake build
```

## References

- Lawson, Michelson — *Spin Geometry* (Princeton, 1989)
- Chevalley — *The Algebraic Theory of Spinors and Clifford Algebras* (Springer, 1996)
- Atiyah, Bott, Shapiro — *Clifford Modules* (Topology, 1964)

## Status

Implemented so far:

- shared Mathlib/notation layer for Clifford, exterior, and quadratic-form work
- totally isotropic subspaces and maximal totally isotropic existence over finite-dimensional fields
- Witt index as the maximal dimension of a totally isotropic subspace
- a canonical maximal-isotropic exterior model `⋀W` with dimension `2 ^ wittIndex`
- the explicit parity splitting `⋀W = ⋀^even W ⊕ ⋀^odd W` for the chosen exterior model
- wedge and contraction operators on the chosen `⋀W` model
- exterior multiplication and contraction flip the chosen even/odd summands
- the split generator action of `W* × W` on `⋀W`, satisfying the hyperbolic Clifford relation
- even split Clifford elements preserve each chosen parity summand, and the restricted split
  spin-group action acts on both halves
- any explicit hyperbolic isometry `Q ≃ dualProd K W` now transports the chosen `⋀W` model to an
  ambient `Cl(V,Q)` action and restricted `spinGroup Q` action
- any explicit hyperbolic presentation `Q ≃ dualProd K W` now also computes the Witt index:
  `wittIndex Q = dim(W)`, via a general bound showing every totally isotropic subspace of
  `dualProd K W` has dimension at most `dim(W)`
- the same explicit hyperbolic presentation also transports the standard split factor `0 × W`
  to a maximal totally isotropic subspace of the ambient quadratic space
- explicit hyperbolic presentations are now packaged as first-class data, carrying their chosen
  `⋀W` spinor model, transported Clifford/spin actions, actual `Module` / `MulAction`
  structures, even/odd halves, Witt-index theorem, and transported maximal isotropic subspace
- a half-dimensional totally isotropic subspace together with a chosen complement now also yields
  such a first-class presentation directly, via
  `QuadraticForm.splitIsometryEquivOfIsCompl` and `HyperbolicPresentation.ofIsCompl`
- more generally, any totally isotropic subspace with a chosen complement now yields a linear
  Witt decomposition `V ≃ W ⊕ W* ⊕ V₀` via
  `QuadraticForm.wittLinearDecompositionOfIsCompl`, together with the residual factor
  `QuadraticForm.wittResidualSubspaceOfIsCompl`; for the canonical chosen Witt subspace, these are
  exposed as `QuadraticForm.wittLinearDecomposition` and `QuadraticForm.wittResidualSubspace`
- that same general chosen-complement setup now also yields the genuine quadratic-form splitting
  `Q ≃ dualProd K W ⊕ Q₀` via `QuadraticForm.wittIsometryEquivOfIsCompl`; for the canonical chosen
  Witt subspace, this is exposed as `QuadraticForm.wittIsometryEquiv`
- that general/canonical Witt splitting is now also packaged through the higher-level presentation
  layer as `Spinor.WittPresentation.ofIsCompl` and `Spinor.WittPresentation.canonical`
- the hyperbolic factor sitting inside the orthogonal complement of the residual term is now exposed
  as `HyperbolicPresentation.wittFactorOfIsCompl` and `HyperbolicPresentation.canonicalWittFactor`,
  so the existing chosen-model Clifford/spin APIs apply directly to that factor too
- when the split isometry is given specifically as `Q ≃ dualProd K Q.wittSubspace`, the canonical
  Witt model now uses that same first-class presentation API and inherits the corresponding
  Clifford/spin module and action structures directly
- in the split-rank Witt-subspace case, the canonical Witt model can now choose a complement
  internally and build its transported Clifford/spin actions directly via `splitWittPresentation`
  and `splitWittSpinRepresentation`
- for nondegenerate finite-dimensional `Q`, the doubled form `Q ⊕ (-Q)` now has a canonical split
  presentation via Mathlib's `QuadraticForm.toDualProd`, upgraded here to an isometry equivalence
  and anchored on the diagonal isotropic subspace of `V × V`
- in that doubled case, the diagonal subspace now realizes the full Witt index and is proved
  maximal totally isotropic
- the doubled canonical split presentation is also exposed as a reusable
  `HyperbolicPresentation (Q ⊕ (-Q))`
- this yields a canonical chosen-model Clifford action, canonical module and spin-group action
  structures, spin representation, and even/odd half-spin spaces for `Q ⊕ (-Q)`, with
  dimensions `2 ^ dim(V)` and `2 ^ (dim(V) - 1)` in positive rank
- in that explicit hyperbolic case, the chosen Witt model now satisfies the expected dimension
  formula `dim = 2 ^ (dim V / 2)`
- for positive Witt index, the chosen even and odd halves of `⋀W` are linearly equivalent and each
  has dimension `2 ^ (dim W - 1)`; hence in the explicit hyperbolic case they have the expected
  half-spin size `2 ^ (dim V / 2 - 1)`
- the induced Clifford action of `Cl(W* × W, dualProd)` on `⋀W` and its restricted split spin-group
  action
- a faithful exterior-model Clifford action obtained from `CliffordAlgebra.equivExterior`
- the induced `spinGroup` representation by restriction
- a chiral decomposition `S = S⁺ ⊕ S⁻` transported from Clifford parity, with `spinGroup`
  preserving both summands and restricting to actions on each summand
- on the zero-form chosen model `⋀W`, an identification of the abstract chiral pieces with the
  explicit even/odd exterior summands `⋀^even W` and `⋀^odd W`
- in the split model, `splitCliffordAction : Cl(W* × W, dualProd) → End(⋀W)` is now proved
  surjective and injective by explicit basis projectors / matrix units
- through `HyperbolicPresentation`, `wittPresentation`, and `splitWittPresentation`, a chosen-model
  positive/negative chiral API on `⋀W` identified with those even/odd summands and carrying the
  corresponding restricted spin representations
- through those same presentation APIs, the transported chosen-model Clifford action on `⋀W` is
  now proved faithful in the explicit hyperbolic, Witt, and split-Witt settings
- in the split model, the full Clifford module `⋀W` is now simple, and that simplicity is
  transported to the explicit hyperbolic, Witt, and split-Witt chosen-model presentations

Still open from the roadmap:

- the final identification of the ambient chiral pieces `S⁺` and `S⁻` with the chosen-model
  submodules `⋀^even W` and `⋀^odd W`
- periodicity, low-dimensional identifications, chiral irreducibility/inequivalence results, and the
  double-cover theorems
- paper-writing and final research-polish tasks

The library currently has a clean `lake build` and zero `sorry` / `admit`.
