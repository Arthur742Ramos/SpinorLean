/- 
  Explicit hyperbolic presentations and the induced chosen spinor model.

  This packages the data `Q ≃ dualProd K W` into a reusable object so downstream constructions can
  talk about the chosen `⋀W` model without carrying a separate subspace and isometry argument
  everywhere.
-/

import Spinor.Chiral
import Spinor.HyperbolicAction

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

@[simp] theorem positiveChiralSpinorModule_eq_evenSpinorModule (P : HyperbolicPresentation Q) :
    P.positiveChiralSpinorModule = P.evenSpinorModule := by
  simpa [positiveChiralSpinorModule, evenSpinorModule] using
    (positiveChiral_zero_eq_evenExteriorSubmodule (K := K) (W := P.W))

@[simp] theorem negativeChiralSpinorModule_eq_oddSpinorModule (P : HyperbolicPresentation Q) :
    P.negativeChiralSpinorModule = P.oddSpinorModule := by
  simpa [negativeChiralSpinorModule, oddSpinorModule] using
    (negativeChiral_zero_eq_oddExteriorSubmodule (K := K) (W := P.W))

/-- The spin action induced by an explicit hyperbolic presentation preserves the positive-chiral
half of the chosen model. -/
theorem spinRepresentation_mem_positiveChiral (P : HyperbolicPresentation Q)
    {g : spinGroup Q} {x : P.spinorModule} (hx : x ∈ P.positiveChiralSpinorModule) :
    P.spinRepresentation g x ∈ P.positiveChiralSpinorModule := by
  have hx' : x ∈ P.evenSpinorModule := by
    simpa [positiveChiralSpinorModule_eq_evenSpinorModule (P := P)] using hx
  have h := P.spinRepresentation_mem_even (g := g) (x := x) hx'
  simpa [positiveChiralSpinorModule_eq_evenSpinorModule (P := P)] using h

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

@[simp] theorem positiveChiralSpinMulAction_smul (P : HyperbolicPresentation Q)
    (g : spinGroup Q) (x : P.positiveChiralSpinorModule) :
    letI := P.positiveChiralSpinMulAction
    g • x = P.positiveChiralSpinRepresentation g x := rfl

/-- The corresponding `spinGroup` action on the negative-chiral half of the presented chosen
model. -/
noncomputable abbrev negativeChiralSpinMulAction (P : HyperbolicPresentation Q) :
    MulAction (spinGroup Q) (P.negativeChiralSpinorModule) :=
  MulAction.compHom (P.negativeChiralSpinorModule) (P.negativeChiralSpinRepresentation)

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
  simpa [HyperbolicPresentation.isotropicSubmodule] using
    hyperbolicIsotropicSubmodule_splitIsometryEquivOfIsCompl
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

end InvertibleTwo
end CanonicalWittPresentation

end Spinor
