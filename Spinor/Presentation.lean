/- 
  Explicit hyperbolic presentations and the induced chosen spinor model.

  This packages the data `Q ≃ dualProd K W` into a reusable object so downstream constructions can
  talk about the chosen `⋀W` model without carrying a separate subspace and isometry argument
  everywhere.
-/

import Spinor.Chiral
import Spinor.HyperbolicAction
import Spinor.OrthogonalAction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# First-class hyperbolic, Witt, and split-Witt presentations

First-class packaging of explicit hyperbolic presentations `Q ≃ dualProd K W` together with
the induced chosen `⋀W` spinor model, Clifford and spin-group actions, even/odd halves, and
matrix-algebra models. Presentations built from split data `(W, U)` or from a chosen Witt
subspace are also exposed here, as are the canonical split-rank constructions that choose a
complement internally.

Every downstream chosen-model Clifford / spin result in the library flows through this
layer: for any `P : HyperbolicPresentation Q`, this file provides a canonical
`Module (CliffordAlgebra Q) P.spinorModule`, a matching `MulAction (spinGroup Q)`, the
identifications of the chiral pieces with `⋀^even W` / `⋀^odd W`, the Witt-index theorem
`wittIndex Q = dim W`, and the canonical endomorphism and matrix-algebra equivalences
`CliffordAlgebra Q ≃ End(⋀W)` and `CliffordAlgebra Q ≃ Mat_(2^dim W)(K)`.

## Main declarations

* `Spinor.HyperbolicPresentation` — the structure packaging `W ≤ V` and `Q ≃ dualProd K W`.
* `HyperbolicPresentation.spinorModule`, `.evenSpinorModule`, `.oddSpinorModule` — the chosen
  `⋀W` model and its chosen parity halves.
* `HyperbolicPresentation.isotropicSubmodule`,
  `HyperbolicPresentation.isotropicSubmodule_isMaximalTotallyIsotropic`,
  `HyperbolicPresentation.wittIndex_eq_finrank` — the transported maximal isotropic subspace
  and the Witt-index theorem.
* `HyperbolicPresentation.cliffordAction`, `HyperbolicPresentation.cliffordModule`,
  `HyperbolicPresentation.spinRepresentation`, `HyperbolicPresentation.spinMulAction` — the
  canonical Clifford and spin-group actions on the chosen model.
* `HyperbolicPresentation.cliffordAction_injective`,
  `HyperbolicPresentation.cliffordEquivEnd`,
  `HyperbolicPresentation.cliffordEquivMatrix` — faithfulness and the endomorphism /
  matrix-algebra packaging of `CliffordAlgebra Q`.
* `HyperbolicPresentation.spinRepresentation_injective`,
  `HyperbolicPresentation.spinRepresentation_not_factor_through_isometry_of_pos_finrank` —
  faithfulness of the chosen-model spin representation and its non-factorization theorem.
* `HyperbolicPresentation.ambientSpinRepresentation_not_factor_through_isometry_of_pos_finrank`,
  `Spinor.splitSpinRepresentation_not_factor_through_isometry` — the corresponding ambient
  regular-model non-factorization theorems in positive split rank.
* `splitSpinorModule`, `positiveHalfSpinorModule`, `negativeHalfSpinorModule` and their
  associated action / simplicity / inequivalence aliases — the top-level split-rank
  canonical chosen-model API built from `HyperbolicPresentation` together with
  `Spinor.WittPresentation` and `Spinor.splitWittPresentation`.
-/

namespace Spinor

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- An explicit split/hyperbolic presentation of a quadratic form. -/
structure HyperbolicPresentation (Q : QuadraticForm K V) where
  W : Submodule K V
  iso : Q.IsometryEquiv (QuadraticForm.dualProd K W)

namespace HyperbolicPresentation

variable {Q : QuadraticForm K V}

/-- The chosen `⋀W` model attached to an explicit hyperbolic presentation. -/
abbrev spinorModule (P : HyperbolicPresentation Q) :=
  IsotropicExteriorModel (K := K) P.W

/-- The even half of the chosen model attached to an explicit hyperbolic presentation. -/
noncomputable abbrev evenSpinorModule (P : HyperbolicPresentation Q) :=
  evenExteriorSubmodule (K := K) P.W

/-- The odd half of the chosen model attached to an explicit hyperbolic presentation. -/
noncomputable abbrev oddSpinorModule (P : HyperbolicPresentation Q) :=
  oddExteriorSubmodule (K := K) P.W

/-- The maximal isotropic subspace transported back from the standard split factor. -/
def isotropicSubmodule (P : HyperbolicPresentation Q) : Submodule K V :=
  hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := P.W) P.iso

/-- The transported split factor is totally isotropic. -/
theorem isotropicSubmodule_isTotallyIsotropic (P : HyperbolicPresentation Q) :
    Q.IsTotallyIsotropic (P.isotropicSubmodule) :=
  hyperbolicIsotropicSubmodule_isTotallyIsotropic (K := K) (Q := Q) (W := P.W) P.iso

/-- The transported isotropic subspace has the expected dimension `dim W`. -/
theorem finrank_isotropicSubmodule (P : HyperbolicPresentation Q) :
    Module.finrank K (P.isotropicSubmodule) = Module.finrank K P.W :=
  finrank_hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := P.W) P.iso

section FiniteDimensional

variable [FiniteDimensional K V]

/-- The chosen `⋀W` model attached to an explicit hyperbolic presentation has the expected size. -/
theorem finrank_spinorModule (P : HyperbolicPresentation Q) :
    Module.finrank K (P.spinorModule) = 2 ^ (Module.finrank K V / 2) :=
  finrank_isotropicExteriorModel_of_hyperbolic (K := K) (Q := Q) (W := P.W) P.iso

section InvertibleTwo

variable [Invertible (2 : K)]

/-- The even half of the chosen `⋀W` model has size `2 ^ (dim W - 1)` in positive split rank. -/
theorem finrank_evenSpinorModule (P : HyperbolicPresentation Q) (hW : 0 < Module.finrank K P.W) :
    Module.finrank K (P.evenSpinorModule) = 2 ^ (Module.finrank K P.W - 1) := by
  simpa [evenSpinorModule] using finrank_evenExterior (K := K) P.W hW

/-- The odd half of the chosen `⋀W` model has size `2 ^ (dim W - 1)` in positive split rank. -/
theorem finrank_oddSpinorModule (P : HyperbolicPresentation Q) (hW : 0 < Module.finrank K P.W) :
    Module.finrank K (P.oddSpinorModule) = 2 ^ (Module.finrank K P.W - 1) := by
  simpa [oddSpinorModule] using finrank_oddExterior (K := K) P.W hW

end InvertibleTwo
end FiniteDimensional

section InvertibleTwo

variable [Invertible (2 : K)]

/-- Any explicit hyperbolic presentation computes the Witt index. -/
theorem wittIndex_eq_finrank [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    Q.wittIndex = Module.finrank K P.W :=
  wittIndex_eq_finrank_of_hyperbolic (K := K) (Q := Q) (W := P.W) P.iso

/-- The transported isotropic subspace is maximal totally isotropic. -/
theorem isotropicSubmodule_isMaximalTotallyIsotropic [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) : Q.IsMaximalTotallyIsotropic (P.isotropicSubmodule) :=
  hyperbolicIsotropicSubmodule_isMaximalTotallyIsotropic
    (K := K) (Q := Q) (W := P.W) P.iso

/-- The Clifford action on the chosen `⋀W` model attached to an explicit hyperbolic presentation. -/
noncomputable def cliffordAction (P : HyperbolicPresentation Q) :
    CliffordAlgebra Q →ₐ[K] Module.End K (P.spinorModule) :=
  hyperbolicCliffordAction (K := K) (Q := Q) (W := P.W) P.iso

/-- The module structure on the chosen `⋀W` model attached to an explicit hyperbolic presentation. -/
abbrev cliffordModule (P : HyperbolicPresentation Q) :
    Module (CliffordAlgebra Q) (P.spinorModule) :=
  hyperbolicModule (K := K) (Q := Q) (W := P.W) P.iso

@[simp] theorem cliffordModule_smul (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra Q) (x : P.spinorModule) :
    letI := P.cliffordModule
    a • x = P.cliffordAction a x := rfl

/-- The spin representation induced by an explicit hyperbolic presentation. -/
noncomputable def spinRepresentation (P : HyperbolicPresentation Q) :
    spinGroup Q →* Module.End K (P.spinorModule) :=
  hyperbolicSpinRepresentation (K := K) (Q := Q) (W := P.W) P.iso

/-- The corresponding `spinGroup` action on the chosen `⋀W` model. -/
abbrev spinMulAction (P : HyperbolicPresentation Q) :
    MulAction (spinGroup Q) (P.spinorModule) :=
  hyperbolicMulAction (K := K) (Q := Q) (W := P.W) P.iso

@[simp] theorem spinMulAction_smul (P : HyperbolicPresentation Q)
    (g : spinGroup Q) (x : P.spinorModule) :
    letI := P.spinMulAction
    g • x = P.spinRepresentation g x := rfl

/-- The induced Clifford action on the presented chosen model satisfies the vector formula. -/
@[simp] theorem cliffordAction_apply_ι (P : HyperbolicPresentation Q) (v : V)
    (x : P.spinorModule) :
    P.cliffordAction (CliffordAlgebra.ι Q v) x = splitGeneratorAction (K := K) P.W (P.iso v) x :=
  hyperbolicCliffordAction_apply_ι (K := K) (Q := Q) (W := P.W) P.iso v x

/-- The presented chosen model satisfies the Clifford relation on vectors. -/
@[simp] theorem cliffordAction_sq_apply (P : HyperbolicPresentation Q) (v : V) (x : P.spinorModule) :
    P.cliffordAction (CliffordAlgebra.ι Q v) (P.cliffordAction (CliffordAlgebra.ι Q v) x) =
      Q v • x :=
  hyperbolicCliffordAction_sq_apply (K := K) (Q := Q) (W := P.W) P.iso v x

/-- The Clifford action attached to an explicit hyperbolic presentation is faithful on the chosen
model `⋀W`. -/
theorem cliffordAction_injective [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    Function.Injective P.cliffordAction := by
  exact hyperbolicCliffordAction_injective (K := K) (Q := Q) (W := P.W) P.iso

/-- The Clifford algebra of an explicit hyperbolic presentation is identified with the full
endomorphism algebra of the chosen model `⋀W`. -/
noncomputable def cliffordEquivEnd [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K P.spinorModule :=
  hyperbolicCliffordEquivEnd (K := K) (Q := Q) (W := P.W) P.iso

@[simp] theorem cliffordEquivEnd_apply [FiniteDimensional K V] (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra Q) :
    P.cliffordEquivEnd a = P.cliffordAction a := rfl

/-- For any finite-dimensional hyperbolic presentation, the kernel of the ambient spin-to-isometry
map is exactly the scalar elements `±1`. -/
theorem spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  refine spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_kernel_scalars
    (Q := Q) ?_ x
  intro y hy
  exact hyperbolicClifford_eq_algebraMap_of_commute (K := K) (Q := Q) (W := P.W) P.iso
    (a := (y : CliffordAlgebra Q))
    (hcomm := commute_of_spinIsometryRepresentation_eq_one (Q := Q) y hy)

/-- Evaluating the presented spin representation is just the presented Clifford action. -/
@[simp] theorem spinRepresentation_apply (P : HyperbolicPresentation Q) (x : spinGroup Q) :
    P.spinRepresentation x = P.cliffordAction x := rfl

/-- The presented spin representation is faithful in finite-dimensional hyperbolic rank. -/
theorem spinRepresentation_injective [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    Function.Injective P.spinRepresentation := by
  intro x y hxy
  apply Subtype.ext
  apply P.cliffordAction_injective
  simpa [spinRepresentation_apply] using hxy

/-- A scalar spin element acts by the matching scalar in any presented chosen model. -/
theorem spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap (P : HyperbolicPresentation Q)
    (x : spinGroup Q) (r : K)
    (hx : (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r) :
    P.spinRepresentation x = algebraMap K (Module.End K P.spinorModule) r := by
  rw [spinRepresentation_apply, hx]
  exact P.cliffordAction.commutes r

/-- Pointwise form of `spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap` for a presented
chosen model. -/
theorem spinRepresentation_apply_of_coe_eq_algebraMap (P : HyperbolicPresentation Q)
    (x : spinGroup Q) (r : K)
    (hx : (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r)
    (v : P.spinorModule) :
    P.spinRepresentation x v = r • v := by
  simpa [Algebra.smul_def] using
    congrArg (fun f : Module.End K P.spinorModule => f v)
      (spinRepresentation_eq_algebraMap_of_coe_eq_algebraMap (K := K) (Q := Q) P x r hx)

@[simp] theorem spinRepresentation_eq_one_iff [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (x : spinGroup Q) :
    P.spinRepresentation x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    exact P.spinRepresentation_injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp

/-- A nontrivial scalar spin element acts nontrivially in any finite-dimensional presented chosen
model. -/
theorem spinRepresentation_ne_one_of_coe_eq_algebraMap_of_ne_one [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (x : spinGroup Q) (r : K)
    (hx : (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r) (hr : r ≠ 1) :
    P.spinRepresentation x ≠ 1 := by
  intro hspin
  have hx1 : x = 1 := (spinRepresentation_eq_one_iff (K := K) (Q := Q) P x).mp hspin
  apply hr
  apply cliffordAlgebraMap_injective (Q := Q)
  calc
    algebraMap K (CliffordAlgebra Q) r = (x : CliffordAlgebra Q) := hx.symm
    _ = ((1 : spinGroup Q) : CliffordAlgebra Q) := by
      exact congrArg (fun y : spinGroup Q => (y : CliffordAlgebra Q)) hx1
    _ = algebraMap K (CliffordAlgebra Q) 1 := rfl

/-- Any kernel witness with nontrivial action on a presented chosen model obstructs factorization of
that presented spin representation through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_kernel_witness
    (P : HyperbolicPresentation Q) (x : spinGroup Q)
    (hker : spinIsometryRepresentation (Q := Q) x = 1) (hspin : P.spinRepresentation x ≠ 1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K P.spinorModule,
        P.spinRepresentation = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  intro hfactor
  rcases hfactor with ⟨ρ, hρ⟩
  have hρx :
      P.spinRepresentation x = ρ (spinIsometryRepresentation (Q := Q) x) := by
    simpa using congrArg
      (fun f : spinGroup Q →* Module.End K P.spinorModule => f x) hρ
  apply hspin
  calc
    P.spinRepresentation x = ρ (spinIsometryRepresentation (Q := Q) x) := hρx
    _ = ρ 1 := by rw [hker]
    _ = 1 := map_one ρ

/-- A nontrivial scalar spin element obstructs factorization of the presented chosen-model spin
representation through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_coe_eq_algebraMap_of_ne_one
    [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (x : spinGroup Q) (r : K)
    (hx : (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r) (hr : r ≠ 1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K P.spinorModule,
        P.spinRepresentation = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  apply spinRepresentation_not_factor_through_isometry_of_kernel_witness (K := K) (Q := Q) P x
  · exact spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x r hx
  · exact spinRepresentation_ne_one_of_coe_eq_algebraMap_of_ne_one (K := K) (Q := Q) P x r hx hr

omit [Invertible (2 : K)] in
/-- Positive hyperbolic rank forces the quadratic form to represent `-1`. -/
theorem exists_quadratic_eq_neg_one [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (hW : 0 < Module.finrank K P.W) :
    ∃ v : V, Q v = -1 := by
  haveI : Nontrivial P.W := Module.nontrivial_of_finrank_pos hW
  obtain ⟨w, hw⟩ := exists_ne (0 : P.W)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hw
  refine ⟨P.iso.symm (-f, w), ?_⟩
  calc
    Q (P.iso.symm (-f, w)) = QuadraticForm.dualProd K P.W (-f, w) := P.iso.symm.map_app (-f, w)
    _ = (-1 : K) := by
      simp [QuadraticForm.dualProd, hf]

/-- If the quadratic form represents `-1`, then the presented chosen-model spin representation does
not factor through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one
    [FiniteDimensional K V] (P : HyperbolicPresentation Q) (hQ : ∃ v : V, Q v = -1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K P.spinorModule,
        P.spinRepresentation = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  have hneq : (-1 : K) ≠ 1 := by
    intro h
    have h' : (0 : K) = 1 + 1 := by
      simpa using congrArg (fun t : K => t + 1) h
    have h2 : (2 : K) = 0 := by
      simpa [one_add_one_eq_two] using h'.symm
    exact two_ne_zero h2
  rcases hQ with ⟨v, hv⟩
  let x : spinGroup Q := ⟨-1, neg_one_mem_spinGroup_of_quadratic_eq_neg_one (Q := Q) v hv⟩
  apply spinRepresentation_not_factor_through_isometry_of_coe_eq_algebraMap_of_ne_one
    (K := K) (Q := Q) P x (-1)
  · change (-1 : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) (-1)
    simp
  · exact hneq

/-- Positive hyperbolic rank obstructs factoring the presented chosen-model spin representation
through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_pos_finrank [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (hW : 0 < Module.finrank K P.W) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K P.spinorModule,
        P.spinRepresentation = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  apply spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one
    (K := K) (Q := Q) P
  exact P.exists_quadratic_eq_neg_one hW

/-- Positive hyperbolic rank also obstructs factoring the ambient regular-model spin representation
through the ambient isometry representation. -/
theorem ambientSpinRepresentation_not_factor_through_isometry_of_pos_finrank [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) (hW : 0 < Module.finrank K P.W) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K (SpinorModule (R := K) (M := V) Q),
        Spinor.spinRepresentation Q = ρ.comp (Spinor.spinIsometryRepresentation (Q := Q)) := by
  have hneq : (-1 : K) ≠ 1 := by
    intro h
    have h' : (0 : K) = 1 + 1 := by
      simpa using congrArg (fun t : K => t + 1) h
    have h2 : (2 : K) = 0 := by
      simpa [one_add_one_eq_two] using h'.symm
    exact two_ne_zero h2
  exact Spinor.spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one
    (Q := Q) (P.exists_quadratic_eq_neg_one hW) hneq

/-- Matrix form of the hyperbolic chosen-model Clifford equivalence. -/
noncomputable def cliffordEquivMatrix [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    CliffordAlgebra Q ≃ₐ[K]
      Matrix (Fin (Module.finrank K P.spinorModule)) (Fin (Module.finrank K P.spinorModule)) K :=
  let b := Module.finBasis K P.W
  letI : FiniteDimensional K P.spinorModule := b.ExteriorAlgebra.finiteDimensional_of_finite
  P.cliffordEquivEnd.trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K P.spinorModule))

/-- Matrix form of the hyperbolic chosen-model Clifford equivalence with an explicit target size. -/
noncomputable def cliffordEquivMatrixOfFinrankEq [FiniteDimensional K V] (P : HyperbolicPresentation Q)
    {n : ℕ} (hn : Module.finrank K P.spinorModule = n) :
    CliffordAlgebra Q ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  let bW := Module.finBasis K P.W
  letI : FiniteDimensional K P.spinorModule := bW.ExteriorAlgebra.finiteDimensional_of_finite
  let b : Module.Basis (Fin n) K P.spinorModule := Module.finBasisOfFinrankEq K P.spinorModule hn
  P.cliffordEquivEnd.trans (LinearMap.toMatrixAlgEquiv b)

/-- The chosen-model Clifford module attached to an explicit hyperbolic presentation is simple. -/
theorem cliffordModule_isSimple [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    letI := P.cliffordModule
    IsSimpleModule (CliffordAlgebra Q) P.spinorModule := by
  exact hyperbolicCliffordAction_isSimpleModule (K := K) (Q := Q) (W := P.W) P.iso

/-- The even Clifford action on the chosen even half attached to an explicit hyperbolic
presentation. -/
noncomputable def evenCliffordAction (P : HyperbolicPresentation Q) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (P.evenSpinorModule) :=
  evenHyperbolicCliffordAction (K := K) (Q := Q) (W := P.W) P.iso

/-- The even Clifford action on the chosen odd half attached to an explicit hyperbolic
presentation. -/
noncomputable def oddCliffordAction (P : HyperbolicPresentation Q) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (P.oddSpinorModule) :=
  oddHyperbolicCliffordAction (K := K) (Q := Q) (W := P.W) P.iso

/-- The even Clifford module structure on the chosen even half attached to an explicit hyperbolic
presentation. -/
noncomputable abbrev evenCliffordModule (P : HyperbolicPresentation Q) :
    Module (CliffordAlgebra.even Q) (P.evenSpinorModule) :=
  evenHyperbolicCliffordModule (K := K) (Q := Q) (W := P.W) P.iso

/-- The even Clifford module structure on the chosen odd half attached to an explicit hyperbolic
presentation. -/
noncomputable abbrev oddCliffordModule (P : HyperbolicPresentation Q) :
    Module (CliffordAlgebra.even Q) (P.oddSpinorModule) :=
  oddHyperbolicCliffordModule (K := K) (Q := Q) (W := P.W) P.iso

@[simp] theorem evenCliffordModule_smul (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra.even Q) (x : P.evenSpinorModule) :
    letI := P.evenCliffordModule
    a • x = P.evenCliffordAction a x := rfl

@[simp] theorem oddCliffordModule_smul (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra.even Q) (x : P.oddSpinorModule) :
    letI := P.oddCliffordModule
    a • x = P.oddCliffordAction a x := rfl

/-- The even Clifford algebra of an explicit hyperbolic presentation is identified with the product
of the endomorphism algebras of the two chosen half-spin modules. -/
noncomputable def evenCliffordEquivProdEnd [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K P.evenSpinorModule × Module.End K P.oddSpinorModule :=
  evenHyperbolicCliffordEquivProdEnd (K := K) (Q := Q) (W := P.W) P.iso

@[simp] theorem evenCliffordEquivProdEnd_apply [FiniteDimensional K V] (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdEnd a = (P.evenCliffordAction a, P.oddCliffordAction a) :=
  rfl

/-- Matrix-product form of the even Clifford algebra of an explicit hyperbolic presentation, using
the two chosen half-spin modules. -/
noncomputable def evenCliffordEquivProdMatrix [FiniteDimensional K V] (P : HyperbolicPresentation Q)
    (hW : 0 < Module.finrank K P.W) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Matrix (Fin (2 ^ (Module.finrank K P.W - 1)))
          (Fin (2 ^ (Module.finrank K P.W - 1))) K ×
        Matrix (Fin (2 ^ (Module.finrank K P.W - 1)))
          (Fin (2 ^ (Module.finrank K P.W - 1))) K := by
  let bW := Module.finBasis K P.W
  letI : FiniteDimensional K P.spinorModule := bW.ExteriorAlgebra.finiteDimensional_of_finite
  let hEven : Module.finrank K P.evenSpinorModule = 2 ^ (Module.finrank K P.W - 1) :=
    finrank_evenSpinorModule (K := K) (Q := Q) P hW
  let hOdd : Module.finrank K P.oddSpinorModule = 2 ^ (Module.finrank K P.W - 1) :=
    finrank_oddSpinorModule (K := K) (Q := Q) P hW
  let bEven :
      Module.Basis (Fin (2 ^ (Module.finrank K P.W - 1))) K P.evenSpinorModule :=
    Module.finBasisOfFinrankEq K P.evenSpinorModule hEven
  let bOdd :
      Module.Basis (Fin (2 ^ (Module.finrank K P.W - 1))) K P.oddSpinorModule :=
    Module.finBasisOfFinrankEq K P.oddSpinorModule hOdd
  exact P.evenCliffordEquivProdEnd.trans
    (AlgEquiv.prodCongr (LinearMap.toMatrixAlgEquiv bEven) (LinearMap.toMatrixAlgEquiv bOdd))

/-- The chosen even half attached to an explicit hyperbolic presentation is simple under the even
Clifford action. -/
theorem evenCliffordModule_isSimple [FiniteDimensional K V] (P : HyperbolicPresentation Q) :
    letI := P.evenCliffordModule
    IsSimpleModule (CliffordAlgebra.even Q) P.evenSpinorModule := by
  exact evenHyperbolicCliffordAction_isSimpleModule
    (K := K) (Q := Q) (W := P.W) P.iso

/-- For positive split rank, the chosen odd half attached to an explicit hyperbolic presentation is
simple under the even Clifford action. -/
theorem oddCliffordModule_isSimple [FiniteDimensional K V] (P : HyperbolicPresentation Q)
    (hW : 0 < Module.finrank K P.W) :
    letI := P.oddCliffordModule
    IsSimpleModule (CliffordAlgebra.even Q) P.oddSpinorModule := by
  exact oddHyperbolicCliffordAction_isSimpleModule
    (K := K) (Q := Q) (W := P.W) P.iso hW

/-- The chosen even and odd halves attached to an explicit hyperbolic presentation are inequivalent
as modules over the even Clifford algebra. -/
theorem not_nonempty_evenOddCliffordLinearEquiv [FiniteDimensional K V]
    (P : HyperbolicPresentation Q) :
    letI := P.evenCliffordModule
    letI := P.oddCliffordModule
    ¬ Nonempty (P.evenSpinorModule ≃ₗ[CliffordAlgebra.even Q] P.oddSpinorModule) := by
  exact not_nonempty_evenOddHyperbolicCliffordLinearEquiv
    (K := K) (Q := Q) (W := P.W) P.iso

/-- The spin action induced by an explicit hyperbolic presentation preserves the even half. -/
theorem spinRepresentation_mem_even (P : HyperbolicPresentation Q)
    {g : spinGroup Q} {x : P.spinorModule} (hx : x ∈ P.evenSpinorModule) :
    P.spinRepresentation g x ∈ P.evenSpinorModule :=
  hyperbolicSpinRepresentation_mem_evenExteriorSubmodule
    (K := K) (Q := Q) (W := P.W) P.iso hx

/-- The spin action induced by an explicit hyperbolic presentation preserves the odd half. -/
theorem spinRepresentation_mem_odd (P : HyperbolicPresentation Q)
    {g : spinGroup Q} {x : P.spinorModule} (hx : x ∈ P.oddSpinorModule) :
    P.spinRepresentation g x ∈ P.oddSpinorModule :=
  hyperbolicSpinRepresentation_mem_oddExteriorSubmodule
    (K := K) (Q := Q) (W := P.W) P.iso hx

/-- The spin representation restricted to the even half of the presented chosen model. -/
noncomputable def evenSpinRepresentation (P : HyperbolicPresentation Q) :
    spinGroup Q →* Module.End K (P.evenSpinorModule) :=
  evenHyperbolicSpinRepresentation (K := K) (Q := Q) (W := P.W) P.iso

/-- The spin representation restricted to the odd half of the presented chosen model. -/
noncomputable def oddSpinRepresentation (P : HyperbolicPresentation Q) :
    spinGroup Q →* Module.End K (P.oddSpinorModule) :=
  oddHyperbolicSpinRepresentation (K := K) (Q := Q) (W := P.W) P.iso

section FiniteDimensional

variable [FiniteDimensional K V]

/-- The positive-chiral half of the chosen model, viewed through the zero-form chiral
identification on `W`. -/
noncomputable abbrev positiveChiralSpinorModule (P : HyperbolicPresentation Q) :=
  positiveChiral (R := K) (M := P.W) (0 : QuadraticForm K P.W)

/-- The negative-chiral half of the chosen model, viewed through the zero-form chiral
identification on `W`. -/
noncomputable abbrev negativeChiralSpinorModule (P : HyperbolicPresentation Q) :=
  negativeChiral (R := K) (M := P.W) (0 : QuadraticForm K P.W)

omit [FiniteDimensional K V] in
@[simp] theorem positiveChiralSpinorModule_eq_evenSpinorModule (P : HyperbolicPresentation Q) :
    P.positiveChiralSpinorModule = P.evenSpinorModule := by
  simpa [positiveChiralSpinorModule, evenSpinorModule] using
    (positiveChiral_zero_eq_evenExteriorSubmodule (K := K) (W := P.W))

omit [FiniteDimensional K V] in
@[simp] theorem negativeChiralSpinorModule_eq_oddSpinorModule (P : HyperbolicPresentation Q) :
    P.negativeChiralSpinorModule = P.oddSpinorModule := by
  simpa [negativeChiralSpinorModule, oddSpinorModule] using
    (negativeChiral_zero_eq_oddExteriorSubmodule (K := K) (W := P.W))

/-- The underlying `K`-linear identification between the positive-chiral half and the even chosen
half of the presented model. -/
noncomputable def positiveChiralLinearEquivEven (P : HyperbolicPresentation Q) :
    P.positiveChiralSpinorModule ≃ₗ[K] P.evenSpinorModule :=
  LinearEquiv.ofEq P.positiveChiralSpinorModule P.evenSpinorModule
    (positiveChiralSpinorModule_eq_evenSpinorModule (P := P))

/-- The underlying `K`-linear identification between the negative-chiral half and the odd chosen
half of the presented model. -/
noncomputable def negativeChiralLinearEquivOdd (P : HyperbolicPresentation Q) :
    P.negativeChiralSpinorModule ≃ₗ[K] P.oddSpinorModule :=
  LinearEquiv.ofEq P.negativeChiralSpinorModule P.oddSpinorModule
    (negativeChiralSpinorModule_eq_oddSpinorModule (P := P))

/-- The even Clifford action on the positive-chiral half of the presented chosen model. -/
noncomputable def positiveChiralCliffordAction (P : HyperbolicPresentation Q) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (P.positiveChiralSpinorModule) :=
  (LinearEquiv.conjAlgEquiv K (P.positiveChiralLinearEquivEven).symm).toAlgHom.comp
    P.evenCliffordAction

/-- The even Clifford action on the negative-chiral half of the presented chosen model. -/
noncomputable def negativeChiralCliffordAction (P : HyperbolicPresentation Q) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (P.negativeChiralSpinorModule) :=
  (LinearEquiv.conjAlgEquiv K (P.negativeChiralLinearEquivOdd).symm).toAlgHom.comp
    P.oddCliffordAction

/-- The even Clifford module structure on the positive-chiral half of the presented chosen model. -/
noncomputable abbrev positiveChiralCliffordModule (P : HyperbolicPresentation Q) :
    Module (CliffordAlgebra.even Q) (P.positiveChiralSpinorModule) :=
  Module.compHom (P.positiveChiralSpinorModule) (P.positiveChiralCliffordAction.toRingHom)

/-- The even Clifford module structure on the negative-chiral half of the presented chosen model. -/
noncomputable abbrev negativeChiralCliffordModule (P : HyperbolicPresentation Q) :
    Module (CliffordAlgebra.even Q) (P.negativeChiralSpinorModule) :=
  Module.compHom (P.negativeChiralSpinorModule) (P.negativeChiralCliffordAction.toRingHom)

omit [FiniteDimensional K V] in
@[simp] theorem positiveChiralCliffordModule_smul (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra.even Q) (x : P.positiveChiralSpinorModule) :
    letI := P.positiveChiralCliffordModule
    a • x = P.positiveChiralCliffordAction a x := rfl

omit [FiniteDimensional K V] in
@[simp] theorem negativeChiralCliffordModule_smul (P : HyperbolicPresentation Q)
    (a : CliffordAlgebra.even Q) (x : P.negativeChiralSpinorModule) :
    letI := P.negativeChiralCliffordModule
    a • x = P.negativeChiralCliffordAction a x := rfl

/-- The positive-chiral/even identification as a linear equivalence of even-Clifford modules. -/
noncomputable def positiveChiralCliffordLinearEquivEven (P : HyperbolicPresentation Q) :
    letI := P.positiveChiralCliffordModule
    letI := P.evenCliffordModule
    P.positiveChiralSpinorModule ≃ₗ[CliffordAlgebra.even Q] P.evenSpinorModule := by
  letI := P.positiveChiralCliffordModule
  letI := P.evenCliffordModule
  refine
    { toFun := P.positiveChiralLinearEquivEven
      invFun := (P.positiveChiralLinearEquivEven).symm
      left_inv := (P.positiveChiralLinearEquivEven).left_inv
      right_inv := (P.positiveChiralLinearEquivEven).right_inv
      map_add' := (P.positiveChiralLinearEquivEven).map_add
      map_smul' := ?_ }
  intro a x
  rw [positiveChiralCliffordModule_smul, evenCliffordModule_smul]
  simp [positiveChiralCliffordAction, LinearEquiv.conjAlgEquiv_apply]

/-- The negative-chiral/odd identification as a linear equivalence of even-Clifford modules. -/
noncomputable def negativeChiralCliffordLinearEquivOdd (P : HyperbolicPresentation Q) :
    letI := P.negativeChiralCliffordModule
    letI := P.oddCliffordModule
    P.negativeChiralSpinorModule ≃ₗ[CliffordAlgebra.even Q] P.oddSpinorModule := by
  letI := P.negativeChiralCliffordModule
  letI := P.oddCliffordModule
  refine
    { toFun := P.negativeChiralLinearEquivOdd
      invFun := (P.negativeChiralLinearEquivOdd).symm
      left_inv := (P.negativeChiralLinearEquivOdd).left_inv
      right_inv := (P.negativeChiralLinearEquivOdd).right_inv
      map_add' := (P.negativeChiralLinearEquivOdd).map_add
      map_smul' := ?_ }
  intro a x
  rw [negativeChiralCliffordModule_smul, oddCliffordModule_smul]
  simp [negativeChiralCliffordAction, LinearEquiv.conjAlgEquiv_apply]

/-- The positive-chiral half of the presented chosen model is simple under the even Clifford
action. -/
theorem positiveChiralCliffordModule_isSimple (P : HyperbolicPresentation Q) :
    letI := P.positiveChiralCliffordModule
    IsSimpleModule (CliffordAlgebra.even Q) P.positiveChiralSpinorModule := by
  letI := P.positiveChiralCliffordModule
  letI := P.evenCliffordModule
  haveI : IsSimpleModule (CliffordAlgebra.even Q) P.evenSpinorModule :=
    P.evenCliffordModule_isSimple
  exact IsSimpleModule.congr (P.positiveChiralCliffordLinearEquivEven)

/-- For positive split rank, the negative-chiral half of the presented chosen model is simple under
the even Clifford action. -/
theorem negativeChiralCliffordModule_isSimple (P : HyperbolicPresentation Q)
    (hW : 0 < Module.finrank K P.W) :
    letI := P.negativeChiralCliffordModule
    IsSimpleModule (CliffordAlgebra.even Q) P.negativeChiralSpinorModule := by
  letI := P.negativeChiralCliffordModule
  letI := P.oddCliffordModule
  haveI : IsSimpleModule (CliffordAlgebra.even Q) P.oddSpinorModule :=
    P.oddCliffordModule_isSimple hW
  exact IsSimpleModule.congr (P.negativeChiralCliffordLinearEquivOdd)

/-- The positive- and negative-chiral halves of the presented chosen model are inequivalent as
modules over the even Clifford algebra. -/
theorem not_nonempty_positiveNegativeChiralCliffordLinearEquiv (P : HyperbolicPresentation Q) :
    letI := P.positiveChiralCliffordModule
    letI := P.negativeChiralCliffordModule
    ¬ Nonempty
      (P.positiveChiralSpinorModule ≃ₗ[CliffordAlgebra.even Q] P.negativeChiralSpinorModule) := by
  intro h
  refine P.not_nonempty_evenOddCliffordLinearEquiv ?_
  rcases h with ⟨e⟩
  exact ⟨((P.positiveChiralCliffordLinearEquivEven).symm.trans e).trans
    (P.negativeChiralCliffordLinearEquivOdd)⟩

omit [FiniteDimensional K V] in
/-- The spin action induced by an explicit hyperbolic presentation preserves the positive-chiral
half of the chosen model. -/
theorem spinRepresentation_mem_positiveChiral (P : HyperbolicPresentation Q)
    {g : spinGroup Q} {x : P.spinorModule} (hx : x ∈ P.positiveChiralSpinorModule) :
    P.spinRepresentation g x ∈ P.positiveChiralSpinorModule := by
  have hx' : x ∈ P.evenSpinorModule := by
    simpa [positiveChiralSpinorModule_eq_evenSpinorModule (P := P)] using hx
  have h := P.spinRepresentation_mem_even (g := g) (x := x) hx'
  simpa [positiveChiralSpinorModule_eq_evenSpinorModule (P := P)] using h

omit [FiniteDimensional K V] in
/-- The spin action induced by an explicit hyperbolic presentation preserves the negative-chiral
half of the chosen model. -/
theorem spinRepresentation_mem_negativeChiral (P : HyperbolicPresentation Q)
    {g : spinGroup Q} {x : P.spinorModule} (hx : x ∈ P.negativeChiralSpinorModule) :
    P.spinRepresentation g x ∈ P.negativeChiralSpinorModule := by
  have hx' : x ∈ P.oddSpinorModule := by
    simpa [negativeChiralSpinorModule_eq_oddSpinorModule (P := P)] using hx
  have h := P.spinRepresentation_mem_odd (g := g) (x := x) hx'
  simpa [negativeChiralSpinorModule_eq_oddSpinorModule (P := P)] using h

/-- The spin representation restricted to the positive-chiral half of the presented chosen model. -/
noncomputable def positiveChiralSpinRepresentation (P : HyperbolicPresentation Q) :
    spinGroup Q →* Module.End K (P.positiveChiralSpinorModule) where
  toFun g :=
    LinearMap.restrict (P.spinRepresentation g)
      (fun x hx => P.spinRepresentation_mem_positiveChiral (g := g) hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

/-- The spin representation restricted to the negative-chiral half of the presented chosen model. -/
noncomputable def negativeChiralSpinRepresentation (P : HyperbolicPresentation Q) :
    spinGroup Q →* Module.End K (P.negativeChiralSpinorModule) where
  toFun g :=
    LinearMap.restrict (P.spinRepresentation g)
      (fun x hx => P.spinRepresentation_mem_negativeChiral (g := g) hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

/-- The corresponding `spinGroup` action on the positive-chiral half of the presented chosen
model. -/
noncomputable abbrev positiveChiralSpinMulAction (P : HyperbolicPresentation Q) :
    MulAction (spinGroup Q) (P.positiveChiralSpinorModule) :=
  MulAction.compHom (P.positiveChiralSpinorModule) (P.positiveChiralSpinRepresentation)

omit [FiniteDimensional K V] in
@[simp] theorem positiveChiralSpinMulAction_smul (P : HyperbolicPresentation Q)
    (g : spinGroup Q) (x : P.positiveChiralSpinorModule) :
    letI := P.positiveChiralSpinMulAction
    g • x = P.positiveChiralSpinRepresentation g x := rfl

/-- The corresponding `spinGroup` action on the negative-chiral half of the presented chosen
model. -/
noncomputable abbrev negativeChiralSpinMulAction (P : HyperbolicPresentation Q) :
    MulAction (spinGroup Q) (P.negativeChiralSpinorModule) :=
  MulAction.compHom (P.negativeChiralSpinorModule) (P.negativeChiralSpinRepresentation)

omit [FiniteDimensional K V] in
@[simp] theorem negativeChiralSpinMulAction_smul (P : HyperbolicPresentation Q)
    (g : spinGroup Q) (x : P.negativeChiralSpinorModule) :
    letI := P.negativeChiralSpinMulAction
    g • x = P.negativeChiralSpinRepresentation g x := rfl

end FiniteDimensional
end InvertibleTwo

section SplitConstructor

variable [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {W U : Submodule K V}

/-- A half-dimensional totally isotropic subspace together with a chosen complement determines a
first-class explicit hyperbolic presentation. -/
noncomputable def ofIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    HyperbolicPresentation Q where
  W := W
  iso := QuadraticForm.splitIsometryEquivOfIsCompl
    (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU

@[simp] theorem ofIsCompl_W
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    (ofIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU).W = W := rfl

@[simp] theorem ofIsCompl_iso
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    (ofIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU).iso =
      QuadraticForm.splitIsometryEquivOfIsCompl
        (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU := rfl

end SplitConstructor

section WittFactorConstructor

variable [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {W U : Submodule K V}

/-- The orthogonal complement of the residual factor in a general Witt splitting carries a
first-class hyperbolic presentation, so the existing chosen-model Clifford/spin APIs apply to that
hyperbolic factor without rebuilding them from scratch. -/
noncomputable def wittFactorOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    HyperbolicPresentation
      (QuadraticForm.orthogonalAmbientWittResidualQuadraticFormOfIsCompl (K := K) Q W U) where
  W := QuadraticForm.orthogonalAmbientWittSubspaceOfIsCompl (K := K) Q W U
  iso :=
    let eW := QuadraticForm.orthogonalAmbientWittSubspaceEquivOfIsCompl (K := K) Q W U
    (QuadraticForm.orthogonalAmbientWittResidualSplitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).trans
      (QuadraticForm.dualProdIsometry (R := K) eW.symm)

@[simp] theorem wittFactorOfIsCompl_W
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    (wittFactorOfIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).W =
      QuadraticForm.orthogonalAmbientWittSubspaceOfIsCompl (K := K) Q W U := rfl

theorem wittFactorOfIsCompl_iso
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    (wittFactorOfIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).iso =
      let eW := QuadraticForm.orthogonalAmbientWittSubspaceEquivOfIsCompl (K := K) Q W U
      (QuadraticForm.orthogonalAmbientWittResidualSplitIsometryEquivOfIsCompl
        (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).trans
        (QuadraticForm.dualProdIsometry (R := K) eW.symm) := rfl

/-- The canonical hyperbolic factor attached to the Witt decomposition of a nondegenerate quadratic
form. -/
noncomputable def canonicalWittFactor (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    HyperbolicPresentation
      (QuadraticForm.orthogonalAmbientWittResidualQuadraticFormOfIsCompl
        (K := K) Q Q.wittSubspace Q.wittSubspaceComplement) :=
  wittFactorOfIsCompl
    (K := K) (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
    hQ Q.wittSubspace_isTotallyIsotropic Q.wittSubspaceComplement_isCompl

@[simp] theorem canonicalWittFactor_W (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (canonicalWittFactor (K := K) Q hQ).W =
      QuadraticForm.orthogonalAmbientWittSubspaceOfIsCompl
        (K := K) Q Q.wittSubspace Q.wittSubspaceComplement := rfl

theorem canonicalWittFactor_iso (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (canonicalWittFactor (K := K) Q hQ).iso =
      let eW := QuadraticForm.orthogonalAmbientWittSubspaceEquivOfIsCompl
        (K := K) Q Q.wittSubspace Q.wittSubspaceComplement
      (QuadraticForm.orthogonalAmbientWittResidualSplitIsometryEquivOfIsCompl
        (K := K) (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
        hQ Q.wittSubspace_isTotallyIsotropic Q.wittSubspaceComplement_isCompl).trans
        (QuadraticForm.dualProdIsometry (R := K) eW.symm) := rfl

end WittFactorConstructor

end HyperbolicPresentation

/-- An explicit general Witt presentation `Q ≃ dualProd K W ⊕ Q₀`, recording both the hyperbolic
Witt subspace and the ambient residual quadratic form. -/
structure WittPresentation (Q : QuadraticForm K V) where
  W : Submodule K V
  residualSubspace : Submodule K V
  iso : Q.IsometryEquiv ((QuadraticForm.dualProd K W).prod (Q.comp residualSubspace.subtype))

namespace WittPresentation

variable {Q : QuadraticForm K V}

/-- The residual quadratic form carried by a Witt presentation. -/
abbrev residualForm (P : WittPresentation Q) : QuadraticForm K P.residualSubspace :=
  Q.comp P.residualSubspace.subtype

section Constructors

variable [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {W U : Submodule K V}

/-- Chosen split data packages the general Witt decomposition as a first-class presentation object. -/
noncomputable def ofIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    WittPresentation Q where
  W := W
  residualSubspace := QuadraticForm.ambientWittResidualSubspaceOfIsCompl (K := K) Q W U
  iso := QuadraticForm.wittIsometryEquivOfIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU

@[simp] theorem ofIsCompl_W
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    (ofIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).W = W := rfl

@[simp] theorem ofIsCompl_residualSubspace
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    (ofIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).residualSubspace =
      QuadraticForm.ambientWittResidualSubspaceOfIsCompl (K := K) Q W U := rfl

@[simp] theorem ofIsCompl_iso
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W) (hWU : IsCompl W U) :
    (ofIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU).iso =
      QuadraticForm.wittIsometryEquivOfIsCompl (K := K) (Q := Q) (W := W) (U := U) hQ hW hWU := rfl

/-- The canonical Witt presentation attached to a nondegenerate quadratic form. -/
noncomputable def canonical (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    WittPresentation Q :=
  ofIsCompl
    (K := K) (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
    hQ Q.wittSubspace_isTotallyIsotropic Q.wittSubspaceComplement_isCompl

@[simp] theorem canonical_W (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (canonical (K := K) Q hQ).W = Q.wittSubspace := rfl

@[simp] theorem canonical_residualSubspace (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (canonical (K := K) Q hQ).residualSubspace =
      QuadraticForm.ambientWittResidualSubspaceOfIsCompl
        (K := K) Q Q.wittSubspace Q.wittSubspaceComplement := rfl

@[simp] theorem canonical_iso (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (canonical (K := K) Q hQ).iso =
      QuadraticForm.wittIsometryEquivOfIsCompl
        (K := K) (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
        hQ Q.wittSubspace_isTotallyIsotropic Q.wittSubspaceComplement_isCompl := rfl

end Constructors
end WittPresentation

section CanonicalWittPresentation

variable [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

/-- The explicit hyperbolic presentation of `Q` using its chosen Witt subspace. -/
noncomputable def wittPresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    HyperbolicPresentation Q where
  W := Q.wittSubspace
  iso := e

@[simp] theorem wittPresentation_W (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    (wittPresentation (K := K) Q e).W = Q.wittSubspace := rfl

@[simp] theorem wittPresentation_iso (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    (wittPresentation (K := K) Q e).iso = e := rfl

section InvertibleTwo

variable [Invertible (2 : K)]

/-- The transported Clifford action on the canonical Witt model packaged through `wittPresentation`. -/
noncomputable def wittCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra Q →ₐ[K] Module.End K (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.cliffordAction (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The module structure on the canonical Witt model induced by an explicit Witt hyperbolic
presentation. -/
noncomputable abbrev wittCliffordModule (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module (CliffordAlgebra Q) (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.cliffordModule (K := K) (Q := Q) (wittPresentation (K := K) Q e)

@[simp] theorem wittCliffordModule_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (a : CliffordAlgebra Q) (x : WittExteriorModel (K := K) Q) :
    letI := wittCliffordModule (K := K) Q e
    a • x = wittCliffordAction (K := K) Q e a x := rfl

/-- The spin representation on the canonical Witt model induced by an explicit Witt hyperbolic
presentation. -/
noncomputable def wittSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    spinGroup Q →* Module.End K (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.spinRepresentation (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The positive-chiral half of the canonical Witt model. -/
noncomputable abbrev positiveWittExterior (Q : QuadraticForm K V) :=
  positiveChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace)

/-- The negative-chiral half of the canonical Witt model. -/
noncomputable abbrev negativeWittExterior (Q : QuadraticForm K V) :=
  negativeChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace)

@[simp] theorem positiveWittExterior_eq_evenWittExterior (Q : QuadraticForm K V) :
    positiveWittExterior (K := K) Q = evenWittExterior (K := K) Q := by
  simpa [positiveWittExterior, evenWittExterior] using
    (positiveChiral_zero_eq_evenExteriorSubmodule (K := K) (W := Q.wittSubspace))

@[simp] theorem negativeWittExterior_eq_oddWittExterior (Q : QuadraticForm K V) :
    negativeWittExterior (K := K) Q = oddWittExterior (K := K) Q := by
  simpa [negativeWittExterior, oddWittExterior] using
    (negativeChiral_zero_eq_oddExteriorSubmodule (K := K) (W := Q.wittSubspace))

/-- The even Clifford action on the positive-chiral half of the canonical Witt model. -/
noncomputable def positiveWittCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralCliffordAction
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The even Clifford action on the negative-chiral half of the canonical Witt model. -/
noncomputable def negativeWittCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralCliffordAction
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The even Clifford module structure on the positive-chiral half of the canonical Witt model. -/
noncomputable abbrev positiveWittCliffordModule (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module (CliffordAlgebra.even Q) (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralCliffordModule
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The even Clifford module structure on the negative-chiral half of the canonical Witt model. -/
noncomputable abbrev negativeWittCliffordModule (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module (CliffordAlgebra.even Q) (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralCliffordModule
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

@[simp] theorem positiveWittCliffordModule_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (a : CliffordAlgebra.even Q) (x : positiveWittExterior (K := K) Q) :
    letI := positiveWittCliffordModule (K := K) Q e
    a • x = positiveWittCliffordAction (K := K) Q e a x := by
  simpa [positiveWittCliffordModule, positiveWittCliffordAction] using
    (HyperbolicPresentation.positiveChiralCliffordModule_smul
      (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) (a := a) (x := x))

@[simp] theorem negativeWittCliffordModule_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (a : CliffordAlgebra.even Q) (x : negativeWittExterior (K := K) Q) :
    letI := negativeWittCliffordModule (K := K) Q e
    a • x = negativeWittCliffordAction (K := K) Q e a x := by
  simpa [negativeWittCliffordModule, negativeWittCliffordAction] using
    (HyperbolicPresentation.negativeChiralCliffordModule_smul
      (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) (a := a) (x := x))

/-- The `spinGroup` action on the canonical Witt model induced by an explicit Witt hyperbolic
presentation. -/
noncomputable abbrev wittSpinMulAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    MulAction (spinGroup Q) (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.spinMulAction (K := K) (Q := Q) (wittPresentation (K := K) Q e)

@[simp] theorem wittSpinMulAction_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (g : spinGroup Q) (x : WittExteriorModel (K := K) Q) :
    letI := wittSpinMulAction (K := K) Q e
    g • x = wittSpinRepresentation (K := K) Q e g x := rfl

/-- The transported Clifford action on the Witt model satisfies the vector formula. -/
@[simp] theorem wittCliffordAction_apply_ι (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (v : V) (x : WittExteriorModel (K := K) Q) :
    wittCliffordAction (K := K) Q e (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) Q.wittSubspace (e v) x := by
  exact HyperbolicPresentation.cliffordAction_apply_ι
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) v x

/-- The transported Clifford action on the Witt model satisfies the Clifford relation on vectors. -/
@[simp] theorem wittCliffordAction_sq_apply (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (v : V) (x : WittExteriorModel (K := K) Q) :
    wittCliffordAction (K := K) Q e (CliffordAlgebra.ι Q v)
        (wittCliffordAction (K := K) Q e (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  exact HyperbolicPresentation.cliffordAction_sq_apply
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) v x

/-- The transported Clifford action on the canonical Witt model is faithful. -/
theorem wittCliffordAction_injective (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Function.Injective (wittCliffordAction (K := K) Q e) := by
  exact HyperbolicPresentation.cliffordAction_injective
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- Endomorphism-algebra form of the Witt-model Clifford equivalence. -/
noncomputable def wittCliffordEquivEnd [FiniteDimensional K V] (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (WittExteriorModel (K := K) Q) :=
  (wittPresentation (K := K) Q e).cliffordEquivEnd

/-- Matrix-algebra form of the Witt-model Clifford equivalence. -/
noncomputable def wittCliffordEquivMatrix [FiniteDimensional K V] (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra Q ≃ₐ[K]
      Matrix (Fin (2 ^ (Module.finrank K V / 2))) (Fin (2 ^ (Module.finrank K V / 2))) K :=
  let hdim : Module.finrank K (WittExteriorModel (K := K) Q) = 2 ^ (Module.finrank K V / 2) :=
    finrank_wittExteriorModel_of_hyperbolic (K := K) Q e
  (wittPresentation (K := K) Q e).cliffordEquivMatrixOfFinrankEq hdim

/-- The transported Clifford module on the canonical Witt model is simple. -/
theorem wittCliffordModule_isSimple (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    letI := wittCliffordModule (K := K) Q e
    IsSimpleModule (CliffordAlgebra Q) (WittExteriorModel (K := K) Q) := by
  exact HyperbolicPresentation.cliffordModule_isSimple
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The transported even Clifford action on the even half of the canonical Witt model. -/
noncomputable def evenWittCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenCliffordAction
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The transported even Clifford action on the odd half of the canonical Witt model. -/
noncomputable def oddWittCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddCliffordAction
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The even Clifford module structure on the even half of the canonical Witt model. -/
noncomputable abbrev evenWittCliffordModule (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module (CliffordAlgebra.even Q) (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenCliffordModule
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The even Clifford module structure on the odd half of the canonical Witt model. -/
noncomputable abbrev oddWittCliffordModule (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module (CliffordAlgebra.even Q) (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddCliffordModule
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

@[simp] theorem evenWittCliffordModule_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (a : CliffordAlgebra.even Q) (x : evenWittExterior (K := K) Q) :
    letI := evenWittCliffordModule (K := K) Q e
    a • x = evenWittCliffordAction (K := K) Q e a x := rfl

@[simp] theorem oddWittCliffordModule_smul (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (a : CliffordAlgebra.even Q) (x : oddWittExterior (K := K) Q) :
    letI := oddWittCliffordModule (K := K) Q e
    a • x = oddWittCliffordAction (K := K) Q e a x := rfl

/-- Product-endomorphism form of the even Clifford algebra on the canonical Witt model. -/
noncomputable def evenWittCliffordEquivProdEnd [FiniteDimensional K V] (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K (evenWittExterior (K := K) Q) ×
        Module.End K (oddWittExterior (K := K) Q) :=
  (wittPresentation (K := K) Q e).evenCliffordEquivProdEnd

/-- Matrix-product form of the even Clifford algebra on the canonical Witt model in the hyperbolic
case. -/
noncomputable def evenWittCliffordEquivProdMatrix [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : 0 < Q.wittIndex) (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Matrix (Fin (2 ^ (Module.finrank K V / 2 - 1)))
          (Fin (2 ^ (Module.finrank K V / 2 - 1))) K ×
        Matrix (Fin (2 ^ (Module.finrank K V / 2 - 1)))
          (Fin (2 ^ (Module.finrank K V / 2 - 1))) K := by
  let bW := Module.finBasis K Q.wittSubspace
  letI : FiniteDimensional K (WittExteriorModel (K := K) Q) :=
    bW.ExteriorAlgebra.finiteDimensional_of_finite
  let hEven : Module.finrank K (evenWittExterior (K := K) Q) =
      2 ^ (Module.finrank K V / 2 - 1) :=
    finrank_evenWittExterior_of_hyperbolic (K := K) Q hQ e
  let hOdd : Module.finrank K (oddWittExterior (K := K) Q) =
      2 ^ (Module.finrank K V / 2 - 1) :=
    finrank_oddWittExterior_of_hyperbolic (K := K) Q hQ e
  let bEven :
      Module.Basis (Fin (2 ^ (Module.finrank K V / 2 - 1))) K (evenWittExterior (K := K) Q) :=
    Module.finBasisOfFinrankEq K (evenWittExterior (K := K) Q) hEven
  let bOdd :
      Module.Basis (Fin (2 ^ (Module.finrank K V / 2 - 1))) K (oddWittExterior (K := K) Q) :=
    Module.finBasisOfFinrankEq K (oddWittExterior (K := K) Q) hOdd
  exact (evenWittCliffordEquivProdEnd (K := K) Q e).trans
    (AlgEquiv.prodCongr (LinearMap.toMatrixAlgEquiv bEven) (LinearMap.toMatrixAlgEquiv bOdd))

/-- The even half of the canonical Witt model is simple under the even Clifford action. -/
theorem evenWittCliffordModule_isSimple (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    letI := evenWittCliffordModule (K := K) Q e
    IsSimpleModule (CliffordAlgebra.even Q) (evenWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.evenCliffordModule_isSimple
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- For positive Witt index, the odd half of the canonical Witt model is simple under the even
Clifford action. -/
theorem oddWittCliffordModule_isSimple (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (hW : 0 < Module.finrank K Q.wittSubspace) :
    letI := oddWittCliffordModule (K := K) Q e
    IsSimpleModule (CliffordAlgebra.even Q) (oddWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.oddCliffordModule_isSimple
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) hW

/-- The chosen even and odd halves of the canonical Witt model are inequivalent under the even
Clifford action. -/
theorem not_nonempty_evenOddWittCliffordLinearEquiv (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    letI := evenWittCliffordModule (K := K) Q e
    letI := oddWittCliffordModule (K := K) Q e
    ¬ Nonempty
      (evenWittExterior (K := K) Q ≃ₗ[CliffordAlgebra.even Q] oddWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.not_nonempty_evenOddCliffordLinearEquiv
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The positive-chiral half of the canonical Witt model is simple under the even Clifford
action. -/
theorem positiveWittCliffordModule_isSimple (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    letI := positiveWittCliffordModule (K := K) Q e
    IsSimpleModule (CliffordAlgebra.even Q) (positiveWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.positiveChiralCliffordModule_isSimple
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- For positive Witt index, the negative-chiral half of the canonical Witt model is simple under
the even Clifford action. -/
theorem negativeWittCliffordModule_isSimple (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    (hW : 0 < Module.finrank K Q.wittSubspace) :
    letI := negativeWittCliffordModule (K := K) Q e
    IsSimpleModule (CliffordAlgebra.even Q) (negativeWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.negativeChiralCliffordModule_isSimple
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) hW

/-- The positive- and negative-chiral halves of the canonical Witt model are inequivalent under
the even Clifford action. -/
theorem not_nonempty_positiveNegativeWittCliffordLinearEquiv (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    letI := positiveWittCliffordModule (K := K) Q e
    letI := negativeWittCliffordModule (K := K) Q e
    ¬ Nonempty
      (positiveWittExterior (K := K) Q ≃ₗ[CliffordAlgebra.even Q] negativeWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.not_nonempty_positiveNegativeChiralCliffordLinearEquiv
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e)

/-- The transported Witt-model spin action preserves the even half. -/
theorem wittSpinRepresentation_mem_even (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ evenWittExterior (K := K) Q) :
    wittSpinRepresentation (K := K) Q e g x ∈ evenWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_even
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) hx

/-- The transported Witt-model spin action preserves the odd half. -/
theorem wittSpinRepresentation_mem_odd (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ oddWittExterior (K := K) Q) :
    wittSpinRepresentation (K := K) Q e g x ∈ oddWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_odd
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) hx

/-- The spin representation on the even half of the canonical Witt model induced by an explicit Witt
hyperbolic presentation. -/
noncomputable def evenWittSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    spinGroup Q →* Module.End K (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenSpinRepresentation
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The spin representation on the odd half of the canonical Witt model induced by an explicit Witt
hyperbolic presentation. -/
noncomputable def oddWittSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    spinGroup Q →* Module.End K (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddSpinRepresentation
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The transported Witt-model spin action preserves the positive-chiral half. -/
theorem wittSpinRepresentation_mem_positiveChiral (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ positiveWittExterior (K := K) Q) :
    wittSpinRepresentation (K := K) Q e g x ∈ positiveWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_positiveChiral
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) (g := g) (x := x) hx

/-- The transported Witt-model spin action preserves the negative-chiral half. -/
theorem wittSpinRepresentation_mem_negativeChiral (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ negativeWittExterior (K := K) Q) :
    wittSpinRepresentation (K := K) Q e g x ∈ negativeWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_negativeChiral
    (K := K) (Q := Q) (P := wittPresentation (K := K) Q e) (g := g) (x := x) hx

/-- The spin representation on the positive-chiral half of the canonical Witt model induced by an
explicit Witt hyperbolic presentation. -/
noncomputable def positiveWittSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    spinGroup Q →* Module.End K (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralSpinRepresentation
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- The spin representation on the negative-chiral half of the canonical Witt model induced by an
explicit Witt hyperbolic presentation. -/
noncomputable def negativeWittSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    spinGroup Q →* Module.End K (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralSpinRepresentation
    (K := K) (Q := Q) (wittPresentation (K := K) Q e)

/-- In the split-rank case, the canonical Witt subspace now determines a hyperbolic presentation
without asking the caller for an explicit isometry. -/
noncomputable def splitWittPresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    HyperbolicPresentation Q :=
  wittPresentation (K := K) Q (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

@[simp] theorem splitWittPresentation_W (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    (splitWittPresentation (K := K) Q hQ hsplit).W = Q.wittSubspace := rfl

@[simp] theorem splitWittPresentation_iso (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    (splitWittPresentation (K := K) Q hQ hsplit).iso =
      QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit := rfl

@[simp] theorem isotropicSubmodule_ofIsCompl
    {W U : Submodule K V} (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    (HyperbolicPresentation.ofIsCompl (K := K) (Q := Q) (W := W) (U := U)
      hQ hW hsplit hWU).isotropicSubmodule = W := by
  exact hyperbolicIsotropicSubmodule_splitIsometryEquivOfIsCompl
    (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU

@[simp] theorem splitWittPresentation_isotropicSubmodule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    (splitWittPresentation (K := K) Q hQ hsplit).isotropicSubmodule = Q.wittSubspace := by
  simpa [splitWittPresentation, HyperbolicPresentation.isotropicSubmodule]
    using hyperbolicIsotropicSubmodule_splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := Q.wittSubspace) (U := Q.wittSubspaceComplement)
      hQ Q.wittSubspace_isTotallyIsotropic
      (by simpa [Q.finrank_wittSubspace] using hsplit)
      Q.wittSubspaceComplement_isCompl

/-- The transported Clifford action on the canonical Witt model in split rank, choosing the
complement internally. -/
noncomputable def splitWittCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra Q →ₐ[K] Module.End K (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.cliffordAction
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The module structure on the canonical Witt model in split rank, choosing the complement
internally. -/
noncomputable abbrev splitWittCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra Q) (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.cliffordModule
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

@[simp] theorem splitWittCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra Q) (x : WittExteriorModel (K := K) Q) :
    letI := splitWittCliffordModule (K := K) Q hQ hsplit
    a • x = splitWittCliffordAction (K := K) Q hQ hsplit a x := rfl

/-- The spin representation on the canonical Witt model in split rank, choosing the complement
internally. -/
noncomputable def splitWittSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.spinRepresentation
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The `spinGroup` action on the canonical Witt model in split rank, choosing the complement
internally. -/
noncomputable abbrev splitWittSpinMulAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    MulAction (spinGroup Q) (WittExteriorModel (K := K) Q) :=
  HyperbolicPresentation.spinMulAction
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

@[simp] theorem splitWittSpinMulAction_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (g : spinGroup Q) (x : WittExteriorModel (K := K) Q) :
    letI := splitWittSpinMulAction (K := K) Q hQ hsplit
    g • x = splitWittSpinRepresentation (K := K) Q hQ hsplit g x := rfl

/-- The split-rank canonical Witt-model Clifford action satisfies the vector formula. -/
@[simp] theorem splitWittCliffordAction_apply_ι (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (v : V) (x : WittExteriorModel (K := K) Q) :
    splitWittCliffordAction (K := K) Q hQ hsplit (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) Q.wittSubspace
        ((splitWittPresentation (K := K) Q hQ hsplit).iso v) x := by
  exact HyperbolicPresentation.cliffordAction_apply_ι
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) v x

/-- The split-rank canonical Witt-model Clifford action satisfies the Clifford relation on
vectors. -/
@[simp] theorem splitWittCliffordAction_sq_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (v : V) (x : WittExteriorModel (K := K) Q) :
    splitWittCliffordAction (K := K) Q hQ hsplit (CliffordAlgebra.ι Q v)
        (splitWittCliffordAction (K := K) Q hQ hsplit (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  exact HyperbolicPresentation.cliffordAction_sq_apply
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) v x

/-- The split-rank canonical Witt-model Clifford action is faithful. -/
theorem splitWittCliffordAction_injective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Function.Injective (splitWittCliffordAction (K := K) Q hQ hsplit) := by
  exact HyperbolicPresentation.cliffordAction_injective
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- Endomorphism-algebra form of the split-rank Witt-model Clifford equivalence. -/
noncomputable def splitWittCliffordEquivEnd [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (WittExteriorModel (K := K) Q) :=
  (splitWittPresentation (K := K) Q hQ hsplit).cliffordEquivEnd

/-- In split rank, the canonical Witt-model Clifford algebra is a full matrix algebra of size
`2^(dim V / 2)`. -/
noncomputable def splitWittCliffordEquivMatrix [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra Q ≃ₐ[K]
      Matrix (Fin (2 ^ (Module.finrank K V / 2))) (Fin (2 ^ (Module.finrank K V / 2))) K :=
  let hdim : Module.finrank K (WittExteriorModel (K := K) Q) = 2 ^ (Module.finrank K V / 2) :=
    finrank_wittExteriorModel_of_hyperbolic (K := K) Q
      (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)
  (splitWittPresentation (K := K) Q hQ hsplit).cliffordEquivMatrixOfFinrankEq hdim

/-- The split-rank canonical Witt-model Clifford module is simple. -/
theorem splitWittCliffordModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := splitWittCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra Q) (WittExteriorModel (K := K) Q) := by
  exact HyperbolicPresentation.cliffordModule_isSimple
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford action on the even half of the canonical Witt model. -/
noncomputable def evenSplitWittCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenCliffordAction
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford action on the odd half of the canonical Witt model. -/
noncomputable def oddSplitWittCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddCliffordAction
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford module structure on the even half of the canonical Witt model. -/
noncomputable abbrev evenSplitWittCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenCliffordModule
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford module structure on the odd half of the canonical Witt model. -/
noncomputable abbrev oddSplitWittCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddCliffordModule
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

@[simp] theorem evenSplitWittCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : evenWittExterior (K := K) Q) :
    letI := evenSplitWittCliffordModule (K := K) Q hQ hsplit
    a • x = evenSplitWittCliffordAction (K := K) Q hQ hsplit a x := rfl

@[simp] theorem oddSplitWittCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : oddWittExterior (K := K) Q) :
    letI := oddSplitWittCliffordModule (K := K) Q hQ hsplit
    a • x = oddSplitWittCliffordAction (K := K) Q hQ hsplit a x := rfl

/-- The split-rank even Clifford action on the positive-chiral half of the canonical Witt model. -/
noncomputable def positiveSplitWittCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralCliffordAction
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford action on the negative-chiral half of the canonical Witt model. -/
noncomputable def negativeSplitWittCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralCliffordAction
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford module structure on the positive-chiral half of the canonical Witt
model. -/
noncomputable abbrev positiveSplitWittCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralCliffordModule
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank even Clifford module structure on the negative-chiral half of the canonical Witt
model. -/
noncomputable abbrev negativeSplitWittCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralCliffordModule
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

@[simp] theorem positiveSplitWittCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : positiveWittExterior (K := K) Q) :
    letI := positiveSplitWittCliffordModule (K := K) Q hQ hsplit
    a • x = positiveSplitWittCliffordAction (K := K) Q hQ hsplit a x := by
  simpa [positiveSplitWittCliffordModule, positiveSplitWittCliffordAction] using
    (HyperbolicPresentation.positiveChiralCliffordModule_smul
      (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) (a := a) (x := x))

@[simp] theorem negativeSplitWittCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : negativeWittExterior (K := K) Q) :
    letI := negativeSplitWittCliffordModule (K := K) Q hQ hsplit
    a • x = negativeSplitWittCliffordAction (K := K) Q hQ hsplit a x := by
  simpa [negativeSplitWittCliffordModule, negativeSplitWittCliffordAction] using
    (HyperbolicPresentation.negativeChiralCliffordModule_smul
      (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) (a := a) (x := x))

/-- Product-endomorphism form of the even Clifford algebra on the canonical Witt model in split
rank. -/
noncomputable def evenSplitWittCliffordEquivProdEnd [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K (evenWittExterior (K := K) Q) ×
        Module.End K (oddWittExterior (K := K) Q) :=
  evenWittCliffordEquivProdEnd (K := K) Q
    (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

/-- Matrix-product form of the even Clifford algebra on the canonical Witt model in split rank. -/
noncomputable def evenSplitWittCliffordEquivProdMatrix [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) (hW : 0 < Q.wittIndex) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Matrix (Fin (2 ^ (Module.finrank K V / 2 - 1)))
          (Fin (2 ^ (Module.finrank K V / 2 - 1))) K ×
        Matrix (Fin (2 ^ (Module.finrank K V / 2 - 1)))
          (Fin (2 ^ (Module.finrank K V / 2 - 1))) K :=
  evenWittCliffordEquivProdMatrix (K := K) Q hW
    (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

/-- The split-rank even half of the canonical Witt model is simple under the even Clifford
action. -/
theorem evenSplitWittCliffordModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := evenSplitWittCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (evenWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.evenCliffordModule_isSimple
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- In split rank, the odd half of the canonical Witt model is simple under the even Clifford
action. -/
theorem oddSplitWittCliffordModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (hW : 0 < Module.finrank K Q.wittSubspace) :
    letI := oddSplitWittCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (oddWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.oddCliffordModule_isSimple
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) hW

/-- In split rank, the chosen even and odd halves of the canonical Witt model are inequivalent
under the even Clifford action. -/
theorem not_nonempty_evenOddSplitWittCliffordLinearEquiv (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := evenSplitWittCliffordModule (K := K) Q hQ hsplit
    letI := oddSplitWittCliffordModule (K := K) Q hQ hsplit
    ¬ Nonempty
      (evenWittExterior (K := K) Q ≃ₗ[CliffordAlgebra.even Q] oddWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.not_nonempty_evenOddCliffordLinearEquiv
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank positive-chiral half of the canonical Witt model is simple under the even
Clifford action. -/
theorem positiveSplitWittCliffordModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := positiveSplitWittCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (positiveWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.positiveChiralCliffordModule_isSimple
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- In split rank, the negative-chiral half of the canonical Witt model is simple under the even
Clifford action. -/
theorem negativeSplitWittCliffordModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (hW : 0 < Module.finrank K Q.wittSubspace) :
    letI := negativeSplitWittCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (negativeWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.negativeChiralCliffordModule_isSimple
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) hW

/-- In split rank, the positive- and negative-chiral halves of the canonical Witt model are
inequivalent under the even Clifford action. -/
theorem not_nonempty_positiveNegativeSplitWittCliffordLinearEquiv (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := positiveSplitWittCliffordModule (K := K) Q hQ hsplit
    letI := negativeSplitWittCliffordModule (K := K) Q hQ hsplit
    ¬ Nonempty
      (positiveWittExterior (K := K) Q ≃ₗ[CliffordAlgebra.even Q] negativeWittExterior (K := K) Q) := by
  exact HyperbolicPresentation.not_nonempty_positiveNegativeChiralCliffordLinearEquiv
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank canonical Witt-model spin action preserves the even half. -/
theorem splitWittSpinRepresentation_mem_even (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ evenWittExterior (K := K) Q) :
    splitWittSpinRepresentation (K := K) Q hQ hsplit g x ∈ evenWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_even
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) hx

/-- The split-rank canonical Witt-model spin action preserves the odd half. -/
theorem splitWittSpinRepresentation_mem_odd (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ oddWittExterior (K := K) Q) :
    splitWittSpinRepresentation (K := K) Q hQ hsplit g x ∈ oddWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_odd
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) hx

/-- The split-rank spin representation on the even half of the canonical Witt model. -/
noncomputable def evenSplitWittSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (evenWittExterior (K := K) Q) :=
  HyperbolicPresentation.evenSpinRepresentation
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank spin representation on the odd half of the canonical Witt model. -/
noncomputable def oddSplitWittSpinRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (oddWittExterior (K := K) Q) :=
  HyperbolicPresentation.oddSpinRepresentation
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank canonical Witt-model spin action preserves the positive-chiral half. -/
theorem splitWittSpinRepresentation_mem_positiveChiral (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ positiveWittExterior (K := K) Q) :
    splitWittSpinRepresentation (K := K) Q hQ hsplit g x ∈ positiveWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_positiveChiral
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)
    (g := g) (x := x) hx

/-- The split-rank canonical Witt-model spin action preserves the negative-chiral half. -/
theorem splitWittSpinRepresentation_mem_negativeChiral (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : WittExteriorModel (K := K) Q}
    (hx : x ∈ negativeWittExterior (K := K) Q) :
    splitWittSpinRepresentation (K := K) Q hQ hsplit g x ∈ negativeWittExterior (K := K) Q := by
  exact HyperbolicPresentation.spinRepresentation_mem_negativeChiral
    (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)
    (g := g) (x := x) hx

/-- The split-rank spin representation on the positive-chiral half of the canonical Witt model. -/
noncomputable def positiveSplitWittSpinRepresentation (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (positiveWittExterior (K := K) Q) :=
  HyperbolicPresentation.positiveChiralSpinRepresentation
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The split-rank spin representation on the negative-chiral half of the canonical Witt model. -/
noncomputable def negativeSplitWittSpinRepresentation (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (negativeWittExterior (K := K) Q) :=
  HyperbolicPresentation.negativeChiralSpinRepresentation
    (K := K) (Q := Q) (splitWittPresentation (K := K) Q hQ hsplit)

/-- The canonical chosen `⋀W` spinor module obtained from the Witt subspace of `Q`. -/
abbrev splitSpinorModule (Q : QuadraticForm K V) :=
  WittExteriorModel (K := K) Q

/-- The canonical positive half-spin module in the split-rank chosen model. -/
noncomputable abbrev positiveHalfSpinorModule (Q : QuadraticForm K V) :=
  positiveWittExterior (K := K) Q

/-- The canonical negative half-spin module in the split-rank chosen model. -/
noncomputable abbrev negativeHalfSpinorModule (Q : QuadraticForm K V) :=
  negativeWittExterior (K := K) Q

/-- The canonical chosen-model Clifford action in split rank. -/
noncomputable def splitSpinorCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra Q →ₐ[K] Module.End K (splitSpinorModule (K := K) Q) :=
  splitWittCliffordAction (K := K) Q hQ hsplit

/-- The canonical chosen-model Clifford module in split rank. -/
noncomputable abbrev splitSpinorCliffordModule (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra Q) (splitSpinorModule (K := K) Q) :=
  splitWittCliffordModule (K := K) Q hQ hsplit

/-- The even Clifford action on the canonical positive half-spin module. -/
noncomputable def positiveHalfSpinorCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (positiveHalfSpinorModule (K := K) Q) :=
  positiveSplitWittCliffordAction (K := K) Q hQ hsplit

/-- The even Clifford action on the canonical negative half-spin module. -/
noncomputable def negativeHalfSpinorCliffordAction (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (negativeHalfSpinorModule (K := K) Q) :=
  negativeSplitWittCliffordAction (K := K) Q hQ hsplit

/-- The even Clifford module structure on the canonical positive half-spin module. -/
noncomputable abbrev positiveHalfSpinorCliffordModule (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (positiveHalfSpinorModule (K := K) Q) :=
  positiveSplitWittCliffordModule (K := K) Q hQ hsplit

/-- The even Clifford module structure on the canonical negative half-spin module. -/
noncomputable abbrev negativeHalfSpinorCliffordModule (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module (CliffordAlgebra.even Q) (negativeHalfSpinorModule (K := K) Q) :=
  negativeSplitWittCliffordModule (K := K) Q hQ hsplit

@[simp] theorem splitSpinorCliffordModule_smul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra Q) (x : splitSpinorModule (K := K) Q) :
    letI := splitSpinorCliffordModule (K := K) Q hQ hsplit
    a • x = splitSpinorCliffordAction (K := K) Q hQ hsplit a x := by
  exact splitWittCliffordModule_smul (K := K) Q hQ hsplit (a := a) (x := x)

@[simp] theorem positiveHalfSpinorCliffordModule_smul (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : positiveHalfSpinorModule (K := K) Q) :
    letI := positiveHalfSpinorCliffordModule (K := K) Q hQ hsplit
    a • x = positiveHalfSpinorCliffordAction (K := K) Q hQ hsplit a x := by
  exact positiveSplitWittCliffordModule_smul (K := K) Q hQ hsplit (a := a) (x := x)

@[simp] theorem negativeHalfSpinorCliffordModule_smul (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (a : CliffordAlgebra.even Q) (x : negativeHalfSpinorModule (K := K) Q) :
    letI := negativeHalfSpinorCliffordModule (K := K) Q hQ hsplit
    a • x = negativeHalfSpinorCliffordAction (K := K) Q hQ hsplit a x := by
  exact negativeSplitWittCliffordModule_smul (K := K) Q hQ hsplit (a := a) (x := x)

/-- The split-rank spin representation on the canonical chosen model. -/
noncomputable def splitSpinorRepresentation (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (splitSpinorModule (K := K) Q) :=
  splitWittSpinRepresentation (K := K) Q hQ hsplit

/-- The split-rank spin representation on the canonical positive half-spin module. -/
noncomputable def positiveHalfSpinRepresentation (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (positiveHalfSpinorModule (K := K) Q) :=
  positiveSplitWittSpinRepresentation (K := K) Q hQ hsplit

/-- The split-rank spin representation on the canonical negative half-spin module. -/
noncomputable def negativeHalfSpinRepresentation (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    spinGroup Q →* Module.End K (negativeHalfSpinorModule (K := K) Q) :=
  negativeSplitWittSpinRepresentation (K := K) Q hQ hsplit

/-- In split rank, the ambient spin-to-isometry kernel is exactly the scalar elements `±1`, stated
on the canonical chosen-model API. -/
theorem splitSpinorCoveringKernel_eq_one_or_neg_one (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex) (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  simpa using
    (HyperbolicPresentation.spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one
      (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) x)

/-- In positive split rank, the canonical chosen-model spin representation does not factor through
the ambient isometry representation. -/
theorem splitSpinorRepresentation_not_factor_through_isometry (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (hW : 0 < Q.wittIndex) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K (splitSpinorModule (K := K) Q),
        splitSpinorRepresentation (K := K) Q hQ hsplit =
          ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  have hW' : 0 < Module.finrank K (splitWittPresentation (K := K) Q hQ hsplit).W := by
    change 0 < Module.finrank K Q.wittSubspace
    rwa [Q.finrank_wittSubspace]
  simpa [splitSpinorRepresentation, splitSpinorModule] using
    (HyperbolicPresentation.spinRepresentation_not_factor_through_isometry_of_pos_finrank
      (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit)
      hW')

/-- In positive split rank, the ambient regular-model spin representation does not factor through
the ambient isometry representation. -/
theorem splitSpinRepresentation_not_factor_through_isometry (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (hW : 0 < Q.wittIndex) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End K (SpinorModule (R := K) (M := V) Q),
        Spinor.spinRepresentation Q = ρ.comp (Spinor.spinIsometryRepresentation (Q := Q)) := by
  have hW' : 0 < Module.finrank K (splitWittPresentation (K := K) Q hQ hsplit).W := by
    change 0 < Module.finrank K Q.wittSubspace
    rwa [Q.finrank_wittSubspace]
  simpa using
    (HyperbolicPresentation.ambientSpinRepresentation_not_factor_through_isometry_of_pos_finrank
      (K := K) (Q := Q) (P := splitWittPresentation (K := K) Q hQ hsplit) hW')

/-- The canonical chosen spinor module is simple in split rank. -/
theorem splitSpinorModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := splitSpinorCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra Q) (splitSpinorModule (K := K) Q) := by
  simpa [splitSpinorCliffordModule, splitSpinorModule] using
    (splitWittCliffordModule_isSimple (K := K) Q hQ hsplit)

/-- The canonical positive half-spin module is simple under the even Clifford algebra in split
rank. -/
theorem positiveHalfSpinorModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := positiveHalfSpinorCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (positiveHalfSpinorModule (K := K) Q) := by
  simpa [positiveHalfSpinorCliffordModule, positiveHalfSpinorModule] using
    (positiveSplitWittCliffordModule_isSimple (K := K) Q hQ hsplit)

/-- In positive split rank, the canonical negative half-spin module is simple under the even
Clifford algebra. -/
theorem negativeHalfSpinorModule_isSimple (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (hW : 0 < Module.finrank K Q.wittSubspace) :
    letI := negativeHalfSpinorCliffordModule (K := K) Q hQ hsplit
    IsSimpleModule (CliffordAlgebra.even Q) (negativeHalfSpinorModule (K := K) Q) := by
  simpa [negativeHalfSpinorCliffordModule, negativeHalfSpinorModule] using
    (negativeSplitWittCliffordModule_isSimple (K := K) Q hQ hsplit hW)

/-- In split rank, the canonical positive and negative half-spin modules are inequivalent as
modules over the even Clifford algebra. -/
theorem not_nonempty_positiveNegativeHalfSpinorCliffordLinearEquiv
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    letI := positiveHalfSpinorCliffordModule (K := K) Q hQ hsplit
    letI := negativeHalfSpinorCliffordModule (K := K) Q hQ hsplit
    ¬ Nonempty
      (positiveHalfSpinorModule (K := K) Q ≃ₗ[CliffordAlgebra.even Q]
        negativeHalfSpinorModule (K := K) Q) := by
  simpa [positiveHalfSpinorCliffordModule, negativeHalfSpinorCliffordModule,
    positiveHalfSpinorModule, negativeHalfSpinorModule] using
    (not_nonempty_positiveNegativeSplitWittCliffordLinearEquiv (K := K) Q hQ hsplit)

/-- The split-rank spin action preserves the canonical positive half-spin module. -/
theorem splitSpinorRepresentation_mem_positiveHalfSpinor (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : splitSpinorModule (K := K) Q}
    (hx : x ∈ positiveHalfSpinorModule (K := K) Q) :
    splitSpinorRepresentation (K := K) Q hQ hsplit g x ∈ positiveHalfSpinorModule (K := K) Q := by
  simpa [splitSpinorRepresentation, splitSpinorModule, positiveHalfSpinorModule] using
    (splitWittSpinRepresentation_mem_positiveChiral (K := K) Q hQ hsplit hx)

/-- The split-rank spin action preserves the canonical negative half-spin module. -/
theorem splitSpinorRepresentation_mem_negativeHalfSpinor (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    {g : spinGroup Q} {x : splitSpinorModule (K := K) Q}
    (hx : x ∈ negativeHalfSpinorModule (K := K) Q) :
    splitSpinorRepresentation (K := K) Q hQ hsplit g x ∈ negativeHalfSpinorModule (K := K) Q := by
  simpa [splitSpinorRepresentation, splitSpinorModule, negativeHalfSpinorModule] using
    (splitWittSpinRepresentation_mem_negativeChiral (K := K) Q hQ hsplit hx)

/-- Top-level dimension formula for the canonical chosen spinor module in split rank. -/
theorem splitSpinorModule_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Module.finrank K (splitSpinorModule (K := K) Q) = 2 ^ (Module.finrank K V / 2) := by
  simpa [splitSpinorModule] using
    finrank_wittExteriorModel_of_hyperbolic (K := K) Q
      (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

/-- Top-level dimension formula for the canonical positive half-spin module in positive split
rank. -/
theorem positiveHalfSpinorModule_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) (hW : 0 < Q.wittIndex) :
    Module.finrank K (positiveHalfSpinorModule (K := K) Q) =
      2 ^ (Module.finrank K V / 2 - 1) := by
  rw [show (positiveHalfSpinorModule (K := K) Q) = evenWittExterior (K := K) Q from
    positiveWittExterior_eq_evenWittExterior Q]
  exact finrank_evenWittExterior_of_hyperbolic (K := K) Q hW
    (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

/-- Top-level dimension formula for the canonical negative half-spin module in positive split
rank. -/
theorem negativeHalfSpinorModule_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) (hW : 0 < Q.wittIndex) :
    Module.finrank K (negativeHalfSpinorModule (K := K) Q) =
      2 ^ (Module.finrank K V / 2 - 1) := by
  rw [show (negativeHalfSpinorModule (K := K) Q) = oddWittExterior (K := K) Q from
    negativeWittExterior_eq_oddWittExterior Q]
  exact finrank_oddWittExterior_of_hyperbolic (K := K) Q hW
    (QuadraticForm.splitWittIsometryEquiv (K := K) Q hQ hsplit)

/-- Top-level Clifford relation on vectors for the canonical chosen-model Clifford action in
split rank. -/
@[simp] theorem splitSpinorCliffordAction_sq_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex)
    (v : V) (x : splitSpinorModule (K := K) Q) :
    splitSpinorCliffordAction (K := K) Q hQ hsplit (CliffordAlgebra.ι Q v)
        (splitSpinorCliffordAction (K := K) Q hQ hsplit (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  simpa [splitSpinorCliffordAction, splitSpinorModule] using
    splitWittCliffordAction_sq_apply (K := K) Q hQ hsplit v x

/-- Top-level faithfulness of the canonical chosen-model Clifford action in split rank. -/
theorem splitSpinorCliffordAction_injective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsplit : Module.finrank K V = 2 * Q.wittIndex) :
    Function.Injective (splitSpinorCliffordAction (K := K) Q hQ hsplit) := by
  simpa [splitSpinorCliffordAction] using
    splitWittCliffordAction_injective (K := K) Q hQ hsplit

/-!
### Identification of the chosen-model half-spin pieces with the ambient chiral submodules

The ambient Z/2-grading on `CliffordAlgebra Q` induces, via `CliffordAlgebra.equivExterior`, the
ambient chiral submodules `positiveChiral`, `negativeChiral` on any exterior-model spinor module
`SpinorModule (R := R) (M := M) Q := ExteriorAlgebra R M`. The canonical chosen-model half-spin
modules `positiveHalfSpinorModule Q`, `negativeHalfSpinorModule Q` are, by construction, exactly
those ambient chiral pieces applied to the spinor module of the zero quadratic form on
`Q.wittSubspace` — i.e. to the zero-form regular spinor module on the chosen Witt subspace
`ExteriorAlgebra K Q.wittSubspace`.

Combined with `positiveChiral_zero_eq_evenExteriorSubmodule` /
`negativeChiral_zero_eq_oddExteriorSubmodule`, this gives the full roadmap-level identification
`S⁺ = ⋀^even W`, `S⁻ = ⋀^odd W`. Note that the ambient `SpinorModule Q = ExteriorAlgebra K V` and
the chosen-model `splitSpinorModule Q = ExteriorAlgebra K Q.wittSubspace` differ in dimension
(`2 ^ dim V` versus `2 ^ (dim V / 2)`), so there is no linear equivalence between them; instead,
the chosen `S⁺`/`S⁻` are the ambient chiral construction transported onto the `(Q.wittSubspace, 0)`
regular spinor data. -/

/-- The canonical chosen-model positive half-spin module `S⁺ = positiveHalfSpinorModule Q` is,
definitionally, the ambient `positiveChiral` submodule of the zero-form exterior-algebra spinor
module on `Q.wittSubspace`. This is the split-rank identification of the chosen even summand with
the ambient chiral module `S⁺` (see `ROADMAP.md` §3.2). -/
theorem positiveHalfSpinorModule_eq_ambient_positiveChiral (Q : QuadraticForm K V) :
    positiveHalfSpinorModule (K := K) Q =
      positiveChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace) :=
  rfl

/-- The canonical chosen-model negative half-spin module `S⁻ = negativeHalfSpinorModule Q` is,
definitionally, the ambient `negativeChiral` submodule of the zero-form exterior-algebra spinor
module on `Q.wittSubspace`. This is the split-rank identification of the chosen odd summand with
the ambient chiral module `S⁻` (see `ROADMAP.md` §3.2). -/
theorem negativeHalfSpinorModule_eq_ambient_negativeChiral (Q : QuadraticForm K V) :
    negativeHalfSpinorModule (K := K) Q =
      negativeChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace) :=
  rfl

/-- Chained identification: the canonical chosen-model positive half-spin module coincides with the
explicit even-degree exterior summand `⋀^even W`, obtained by routing the ambient `positiveChiral`
identification through the zero-form equivalence `positiveChiral_zero_eq_evenExteriorSubmodule`. -/
theorem positiveHalfSpinorModule_eq_evenWittExterior (Q : QuadraticForm K V) :
    positiveHalfSpinorModule (K := K) Q = evenWittExterior (K := K) Q :=
  positiveWittExterior_eq_evenWittExterior Q

/-- Chained identification: the canonical chosen-model negative half-spin module coincides with the
explicit odd-degree exterior summand `⋀^odd W`, obtained by routing the ambient `negativeChiral`
identification through the zero-form equivalence `negativeChiral_zero_eq_oddExteriorSubmodule`. -/
theorem negativeHalfSpinorModule_eq_oddWittExterior (Q : QuadraticForm K V) :
    negativeHalfSpinorModule (K := K) Q = oddWittExterior (K := K) Q :=
  negativeWittExterior_eq_oddWittExterior Q

/-- Underlying `K`-linear identification between the canonical chosen-model positive half-spin
module (viewed as the ambient `positiveChiral` piece of the zero-form spinor module on
`Q.wittSubspace`) and the explicit even-degree exterior summand `⋀^even W`. -/
noncomputable def positiveHalfSpinorModuleLinearEquivEvenWittExterior (Q : QuadraticForm K V) :
    positiveHalfSpinorModule (K := K) Q ≃ₗ[K] evenWittExterior (K := K) Q :=
  LinearEquiv.ofEq _ _ (positiveHalfSpinorModule_eq_evenWittExterior (K := K) Q)

/-- Underlying `K`-linear identification between the canonical chosen-model negative half-spin
module (viewed as the ambient `negativeChiral` piece of the zero-form spinor module on
`Q.wittSubspace`) and the explicit odd-degree exterior summand `⋀^odd W`. -/
noncomputable def negativeHalfSpinorModuleLinearEquivOddWittExterior (Q : QuadraticForm K V) :
    negativeHalfSpinorModule (K := K) Q ≃ₗ[K] oddWittExterior (K := K) Q :=
  LinearEquiv.ofEq _ _ (negativeHalfSpinorModule_eq_oddWittExterior (K := K) Q)

/-- Packaged bridge theorem closing ROADMAP §3.2 line 107: in split rank, the canonical chosen
even/odd summands `⋀^even W` / `⋀^odd W` coincide with the ambient chiral submodules `S⁺` / `S⁻`
of the zero-form regular spinor module `ExteriorAlgebra K Q.wittSubspace = splitSpinorModule Q`. -/
theorem splitSpinor_chiral_correspondence (Q : QuadraticForm K V) :
    positiveHalfSpinorModule (K := K) Q =
        positiveChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace) ∧
      negativeHalfSpinorModule (K := K) Q =
        negativeChiral (R := K) (M := Q.wittSubspace) (0 : QuadraticForm K Q.wittSubspace) ∧
      positiveHalfSpinorModule (K := K) Q = evenWittExterior (K := K) Q ∧
      negativeHalfSpinorModule (K := K) Q = oddWittExterior (K := K) Q :=
  ⟨positiveHalfSpinorModule_eq_ambient_positiveChiral (K := K) Q,
    negativeHalfSpinorModule_eq_ambient_negativeChiral (K := K) Q,
    positiveHalfSpinorModule_eq_evenWittExterior (K := K) Q,
    negativeHalfSpinorModule_eq_oddWittExterior (K := K) Q⟩

end InvertibleTwo
end CanonicalWittPresentation

end Spinor
