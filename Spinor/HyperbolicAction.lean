/- 
  Transport the chosen `⋀W` model along an explicit hyperbolic isometry.

  This provides the ambient Clifford and spin actions on `⋀W` whenever the quadratic form `Q`
  is presented by an explicit isometry `Q ≃ dualProd K W`. It is the split/hyperbolic transport
  layer that sits between the raw `W* × W` model and the still-open full Witt decomposition.
-/

import Spinor.ExteriorModel

namespace Spinor

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

section GradingTransport

variable {Q : QuadraticForm K V} {W : Submodule K V}

/-- An isometric map to the split hyperbolic model preserves the even Clifford grading. -/
theorem cliffordMap_mem_evenOdd_zero
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.evenOdd Q 0) :
    CliffordAlgebra.map e.toIsometry a ∈
      CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 0 := by
  refine CliffordAlgebra.even_induction (Q := Q) ?_ ?_ ?_ a ha
  · intro r
    simpa using
      (SetLike.algebraMap_mem_graded (CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W)) r)
  · intro x y hx hy ihx ihy
    simpa [map_add] using Submodule.add_mem _ ihx ihy
  · intro m₁ m₂ x hx ih
    simpa [map_mul, CliffordAlgebra.map_apply_ι, mul_assoc] using
      SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := QuadraticForm.dualProd K W) (e m₁) (e m₂))
        ih

/-- An isometric map to the split hyperbolic model preserves the odd Clifford grading. -/
theorem cliffordMap_mem_evenOdd_one
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.evenOdd Q 1) :
    CliffordAlgebra.map e.toIsometry a ∈
      CliffordAlgebra.evenOdd (QuadraticForm.dualProd K W) 1 := by
  refine CliffordAlgebra.odd_induction (Q := Q) ?_ ?_ ?_ a ha
  · intro v
    simpa [CliffordAlgebra.map_apply_ι] using
      (CliffordAlgebra.ι_mem_evenOdd_one (Q := QuadraticForm.dualProd K W) (e v))
  · intro x y hx hy ihx ihy
    simpa [map_add] using Submodule.add_mem _ ihx ihy
  · intro m₁ m₂ x hx ih
    simpa [map_mul, CliffordAlgebra.map_apply_ι, mul_assoc] using
      SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := QuadraticForm.dualProd K W) (e m₁) (e m₂))
        ih

end GradingTransport

section HyperbolicTransport

variable [Invertible (2 : K)]
variable {Q : QuadraticForm K V} {W : Submodule K V}

/-- Transport the split Clifford action on `⋀W` along a chosen hyperbolic isometry. -/
def hyperbolicCliffordAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra Q →ₐ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  (splitCliffordAction (K := K) W).comp (CliffordAlgebra.map e.toIsometry)

@[simp]
theorem hyperbolicCliffordAction_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra Q) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e a x =
      splitCliffordAction (K := K) W (CliffordAlgebra.map e.toIsometry a) x := by
  rfl

@[simp]
theorem hyperbolicCliffordAction_apply_ι
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) W (e v) x := by
  simp [hyperbolicCliffordAction]

/-- The transported hyperbolic action satisfies the Clifford relation on vectors. -/
@[simp]
theorem hyperbolicCliffordAction_ι_sq
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (v : V) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) *
        hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) =
      algebraMap K (Module.End K (IsotropicExteriorModel (K := K) W)) (Q v) := by
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, AlgHom.commutes]

@[simp]
theorem hyperbolicCliffordAction_sq_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (v : V)
    (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v)
        (hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  simpa [hyperbolicCliffordAction_apply_ι, e.map_app v] using
    splitGeneratorAction_sq_apply (K := K) (W := W) (d := (e v).1) (w := (e v).2) (x := x)

/-- The module structure on `⋀W` induced by a hyperbolic isometry `Q ≃ dualProd`. -/
abbrev hyperbolicModule (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module (CliffordAlgebra Q) (IsotropicExteriorModel (K := K) W) :=
  Module.compHom (IsotropicExteriorModel (K := K) W)
    (hyperbolicCliffordAction (K := K) (W := W) e).toRingHom

/-- Restrict the transported hyperbolic Clifford action on `⋀W` to the spin group of `Q`. -/
def hyperbolicSpinRepresentation (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (IsotropicExteriorModel (K := K) W) :=
  (hyperbolicCliffordAction (K := K) (W := W) e).toMonoidHom.comp (SubmonoidClass.subtype (spinGroup Q))

@[simp]
theorem hyperbolicSpinRepresentation_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (g : spinGroup Q) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g =
      hyperbolicCliffordAction (K := K) (W := W) e g := rfl

/-- The spin action on `⋀W` induced by a hyperbolic isometry `Q ≃ dualProd`. -/
abbrev hyperbolicMulAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    MulAction (spinGroup Q) (IsotropicExteriorModel (K := K) W) :=
  MulAction.compHom (IsotropicExteriorModel (K := K) W)
    (hyperbolicSpinRepresentation (K := K) (W := W) e)

/-- The transported hyperbolic spin action preserves the chosen even summand. -/
theorem hyperbolicSpinRepresentation_mem_evenExteriorSubmodule
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {g : spinGroup Q}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g x ∈ evenExteriorSubmodule (K := K) W := by
  simpa [hyperbolicSpinRepresentation, hyperbolicCliffordAction] using
    splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W)
      (a := CliffordAlgebra.map e.toIsometry (g : CliffordAlgebra Q))
      (cliffordMap_mem_evenOdd_zero (K := K) (W := W) e (spinGroup.mem_even g.property)) hx

/-- The transported hyperbolic spin action preserves the chosen odd summand. -/
theorem hyperbolicSpinRepresentation_mem_oddExteriorSubmodule
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {g : spinGroup Q}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g x ∈ oddExteriorSubmodule (K := K) W := by
  simpa [hyperbolicSpinRepresentation, hyperbolicCliffordAction] using
    splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W)
      (a := CliffordAlgebra.map e.toIsometry (g : CliffordAlgebra Q))
      (cliffordMap_mem_evenOdd_zero (K := K) (W := W) e (spinGroup.mem_even g.property)) hx

/-- The transported hyperbolic spin representation restricted to the chosen even summand. -/
noncomputable def evenHyperbolicSpinRepresentation
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (evenExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (hyperbolicSpinRepresentation (K := K) (W := W) e g)
      (fun x hx => hyperbolicSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := W) e hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

/-- The transported hyperbolic spin representation restricted to the chosen odd summand. -/
noncomputable def oddHyperbolicSpinRepresentation
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (oddExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (hyperbolicSpinRepresentation (K := K) (W := W) e g)
      (fun x hx => hyperbolicSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := W) e hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

section SplitTransport

variable [FiniteDimensional K V]
variable {U : Submodule K V}

/-- Transport the chosen `⋀W` Clifford action directly from split data
`W ≤ V` plus a chosen complement `U`. -/
noncomputable def hyperbolicCliffordActionOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    CliffordAlgebra Q →ₐ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  hyperbolicCliffordAction (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- The module structure on `⋀W` induced directly from split data `W ⊔ U = V`. -/
noncomputable abbrev hyperbolicModuleOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Module (CliffordAlgebra Q) (IsotropicExteriorModel (K := K) W) :=
  hyperbolicModule (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- Restrict the split-data Clifford action on `⋀W` to the ambient spin group. -/
noncomputable def hyperbolicSpinRepresentationOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    spinGroup Q →* Module.End K (IsotropicExteriorModel (K := K) W) :=
  hyperbolicSpinRepresentation (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- The ambient `spinGroup Q` action on `⋀W` induced directly from split data. -/
noncomputable abbrev hyperbolicMulActionOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    MulAction (spinGroup Q) (IsotropicExteriorModel (K := K) W) :=
  hyperbolicMulAction (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

@[simp]
theorem hyperbolicCliffordActionOfIsCompl_apply_ι
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) W
        (QuadraticForm.splitIsometryEquivOfIsCompl
          (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU v) x := by
  exact hyperbolicCliffordAction_apply_ι
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    v x

@[simp]
theorem hyperbolicCliffordActionOfIsCompl_sq_apply
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU (CliffordAlgebra.ι Q v)
        (hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
          hQ hW hsplit hWU (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  exact hyperbolicCliffordAction_sq_apply
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    v x

/-- The split-data ambient spin action preserves the even half of `⋀W`. -/
theorem hyperbolicSpinRepresentationOfIsCompl_mem_evenExteriorSubmodule
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    {g : spinGroup Q} {x : IsotropicExteriorModel (K := K) W}
    (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentationOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
      hQ hW hsplit hWU g x ∈ evenExteriorSubmodule (K := K) W := by
  exact hyperbolicSpinRepresentation_mem_evenExteriorSubmodule
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    hx

/-- The split-data ambient spin action preserves the odd half of `⋀W`. -/
theorem hyperbolicSpinRepresentationOfIsCompl_mem_oddExteriorSubmodule
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    {g : spinGroup Q} {x : IsotropicExteriorModel (K := K) W}
    (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentationOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
      hQ hW hsplit hWU g x ∈ oddExteriorSubmodule (K := K) W := by
  exact hyperbolicSpinRepresentation_mem_oddExteriorSubmodule
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    hx

end SplitTransport

section WittModel

variable [FiniteDimensional K V]

/-- The transported hyperbolic Clifford action on the canonical Witt model. -/
noncomputable def wittHyperbolicCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  hyperbolicCliffordAction (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation on the canonical Witt model. -/
noncomputable def wittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  hyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation restricted to the even Witt summand. -/
noncomputable abbrev evenWittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  evenHyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation restricted to the odd Witt summand. -/
noncomputable abbrev oddWittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  oddHyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin action preserves the even half of the canonical Witt model. -/
theorem wittHyperbolicSpinRepresentation_mem_evenWittExterior (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ evenWittExterior (K := K) Q) :
    wittHyperbolicSpinRepresentation (K := K) Q e g x ∈ evenWittExterior (K := K) Q := by
  exact hyperbolicSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := Q.wittSubspace) e hx

/-- The transported hyperbolic spin action preserves the odd half of the canonical Witt model. -/
theorem wittHyperbolicSpinRepresentation_mem_oddWittExterior (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ oddWittExterior (K := K) Q) :
    wittHyperbolicSpinRepresentation (K := K) Q e g x ∈ oddWittExterior (K := K) Q := by
  exact hyperbolicSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := Q.wittSubspace) e hx

end WittModel

end HyperbolicTransport

section SplitUnitGenerator

variable [FiniteDimensional K V]
variable {W : Submodule K V}

/-- If `W` is nonzero, one can choose a split generator with square equal to the identity. -/
lemma exists_splitUnitGenerator (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    ∃ d : Module.Dual K W, ∃ w : W, d w = 1 := by
  let b := Module.finBasis K W
  let i : Fin (Module.finrank K W) := ⟨0, hW⟩
  refine ⟨b.coord i, b i, ?_⟩
  simp [b, i]
end SplitUnitGenerator

section SplitGeneratorInvolution

variable [Invertible (2 : K)]
variable {W : Submodule K V}

/-- A split generator with `d(w) = 1` acts as an involution on `⋀W`. -/
lemma splitGeneratorAction_sq_apply_of_dual_one (W : Submodule K V)
    (d : Module.Dual K W) (w : W)
    (h : d w = 1) (x : IsotropicExteriorModel (K := K) W) :
    splitGeneratorAction (K := K) W (d, w)
        (splitGeneratorAction (K := K) W (d, w) x) = x := by
  simpa [QuadraticForm.dualProd, h] using
    splitGeneratorAction_sq_apply (K := K) (W := W) (d := d) (w := w) (x := x)

end SplitGeneratorInvolution

section EvenOddDimensions

variable [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {W : Submodule K V}

/-- For positive Witt index, a split unit generator swaps the chosen even and odd halves of `⋀W`. -/
noncomputable def evenOddSwapEquiv (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    evenExteriorSubmodule (K := K) W ≃ₗ[K] oddExteriorSubmodule (K := K) W := by
  classical
  let d : Module.Dual K W := Classical.choose (exists_splitUnitGenerator (K := K) W hW)
  let w : W := Classical.choose (Classical.choose_spec (exists_splitUnitGenerator (K := K) W hW))
  have hdw : d w = 1 :=
    Classical.choose_spec (Classical.choose_spec (exists_splitUnitGenerator (K := K) W hW))
  let toOdd : evenExteriorSubmodule (K := K) W →ₗ[K] oddExteriorSubmodule (K := K) W :=
    { toFun := fun x => ⟨splitGeneratorAction (K := K) W (d, w) x,
        splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) (d, w) x.property⟩
      map_add' := by
        intro x y
        ext
        simp [map_add]
      map_smul' := by
        intro a x
        ext
        simp [map_smul] }
  let toEven : oddExteriorSubmodule (K := K) W →ₗ[K] evenExteriorSubmodule (K := K) W :=
    { toFun := fun x => ⟨splitGeneratorAction (K := K) W (d, w) x,
        splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) (d, w) x.property⟩
      map_add' := by
        intro x y
        ext
        simp [map_add]
      map_smul' := by
        intro a x
        ext
        simp [map_smul] }
  refine
    { toLinearMap := toOdd
      invFun := toEven
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    ext
    exact splitGeneratorAction_sq_apply_of_dual_one (K := K) (W := W) d w hdw x
  · intro x
    ext
    exact splitGeneratorAction_sq_apply_of_dual_one (K := K) (W := W) d w hdw x

/-- For positive Witt index, the chosen even and odd halves of `⋀W` have the same dimension. -/
theorem finrank_evenExterior_eq_finrank_oddExterior (W : Submodule K V)
    (hW : 0 < Module.finrank K W) :
    Module.finrank K (evenExteriorSubmodule (K := K) W) =
      Module.finrank K (oddExteriorSubmodule (K := K) W) := by
  exact LinearEquiv.finrank_eq (evenOddSwapEquiv (K := K) W hW)

/-- For positive Witt index, the chosen even half of `⋀W` has dimension `2^(dim W - 1)`. -/
theorem finrank_evenExterior (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    Module.finrank K (evenExteriorSubmodule (K := K) W) = 2 ^ (Module.finrank K W - 1) := by
  let b := Module.finBasis K W
  letI : FiniteDimensional K (IsotropicExteriorModel (K := K) W) :=
    b.ExteriorAlgebra.finiteDimensional_of_finite
  letI : FiniteDimensional K (evenExteriorSubmodule (K := K) W) := by infer_instance
  letI : FiniteDimensional K (oddExteriorSubmodule (K := K) W) := by infer_instance
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (evenExteriorSubmodule (K := K) W) (oddExteriorSubmodule (K := K) W)
  rw [evenExteriorSubmodule_sup_oddExteriorSubmodule, evenExteriorSubmodule_inf_oddExteriorSubmodule,
    finrank_top, finrank_bot, add_zero, finrank_isotropicExteriorModel] at hsum
  have hEq := finrank_evenExterior_eq_finrank_oddExterior (K := K) W hW
  have hsum' : Module.finrank K (evenExteriorSubmodule (K := K) W) +
      Module.finrank K (evenExteriorSubmodule (K := K) W) = 2 ^ Module.finrank K W := by
    simpa [hEq] using hsum.symm
  have hpow : 2 ^ Module.finrank K W = 2 * 2 ^ (Module.finrank K W - 1) := by
    have hW0 : Module.finrank K W ≠ 0 := Nat.ne_of_gt hW
    rcases Nat.exists_eq_succ_of_ne_zero hW0 with ⟨n, hn⟩
    rw [hn]
    simp [pow_succ, mul_comm]
  have hsum'' : 2 * Module.finrank K (evenExteriorSubmodule (K := K) W) =
      2 ^ Module.finrank K W := by
    simpa [two_mul] using hsum'
  have htwice : 2 * Module.finrank K (evenExteriorSubmodule (K := K) W) =
      2 * 2 ^ (Module.finrank K W - 1) := hsum''.trans hpow
  have htwice' : Module.finrank K (evenExteriorSubmodule (K := K) W) * 2 =
      2 ^ (Module.finrank K W - 1) * 2 := by
    simpa [mul_comm] using htwice
  exact Nat.mul_right_cancel (by decide : 0 < 2) htwice'

/-- For positive Witt index, the chosen odd half of `⋀W` has dimension `2^(dim W - 1)`. -/
theorem finrank_oddExterior (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    Module.finrank K (oddExteriorSubmodule (K := K) W) = 2 ^ (Module.finrank K W - 1) := by
  rw [← finrank_evenExterior_eq_finrank_oddExterior (K := K) W hW]
  exact finrank_evenExterior (K := K) W hW

end EvenOddDimensions

section HyperbolicDimensions

variable {Q : QuadraticForm K V} {W : Submodule K V}

section SplitIsotropicSubmodule

/-- The standard totally isotropic factor `0 × W` inside the split hyperbolic space `W* × W`. -/
def splitIsotropicSubmodule (W : Submodule K V) : Submodule K (Module.Dual K W × W) :=
  LinearMap.range (LinearMap.inr K (Module.Dual K W) W)

/-- The standard split factor `0 × W` is totally isotropic in `W* × W`. -/
theorem splitIsotropicSubmodule_isTotallyIsotropic (W : Submodule K V) :
    (QuadraticForm.dualProd K W).IsTotallyIsotropic (splitIsotropicSubmodule (K := K) (V := V) W) := by
  intro x
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨w, rfl⟩
  simp [QuadraticForm.dualProd]

/-- An explicit hyperbolic presentation carries the standard split factor to an ambient subspace. -/
def hyperbolicIsotropicSubmodule {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) : Submodule K V :=
  (splitIsotropicSubmodule (K := K) (V := V) W).map e.symm.toLinearMap

/-- The isotropic subspace carried by an explicit hyperbolic presentation is totally isotropic. -/
theorem hyperbolicIsotropicSubmodule_isTotallyIsotropic {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.IsTotallyIsotropic (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) := by
  dsimp [hyperbolicIsotropicSubmodule]
  exact (splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W).map e.symm

/-- The isotropic subspace carried by an explicit hyperbolic presentation has the expected rank. -/
theorem finrank_hyperbolicIsotropicSubmodule {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) =
      Module.finrank K W := by
  dsimp [hyperbolicIsotropicSubmodule]
  calc
    Module.finrank K ((splitIsotropicSubmodule (K := K) (V := V) W).map e.symm.toLinearMap) =
        Module.finrank K (splitIsotropicSubmodule (K := K) (V := V) W) := by
          exact LinearEquiv.finrank_map_eq e.symm.toLinearEquiv _
    _ = Module.finrank K W := by
      simpa [splitIsotropicSubmodule] using
        LinearMap.finrank_range_of_inj
          (f := LinearMap.inr K (Module.Dual K W) W)
          LinearMap.inr_injective

@[simp] theorem hyperbolicIsotropicSubmodule_splitIsometryEquivOfIsCompl
    [FiniteDimensional K V] [Invertible (2 : K)] {Q : QuadraticForm K V} {W U : Submodule K V}
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W)
      (QuadraticForm.splitIsometryEquivOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU) = W := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    rcases hx with ⟨w, rfl⟩
    simpa using (w : V).2
  · intro hv
    refine ⟨(0, ⟨v, hv⟩), ?_, ?_⟩
    · exact ⟨⟨v, hv⟩, rfl⟩
    · simpa using
        (QuadraticForm.splitIsometryEquivOfIsCompl_symm_inr (K := K) (Q := Q) (W := W) (U := U)
          hQ hW hsplit hWU ⟨v, hv⟩)

end SplitIsotropicSubmodule

section HyperbolicWittIndex

variable [Invertible (2 : K)]

/-- The split hyperbolic form on `W* × W` is nondegenerate. -/
theorem dualProd_nondegenerate (W : Submodule K V) :
    (QuadraticForm.dualProd K W).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  ext x
  constructor
  · intro hx
    rcases (QuadraticMap.mem_radical_iff'.mp hx) with ⟨hxQ, hxrad⟩
    have hxQ' : x.1 x.2 = 0 := by
      simpa [QuadraticForm.dualProd] using hxQ
    have hx₁ : x.1 = 0 := by
      ext w
      have htest := hxrad (0, w)
      simpa [QuadraticForm.dualProd, hxQ'] using htest
    have hx₂eval : Module.Dual.eval K W x.2 = 0 := by
      ext d
      have htest := hxrad (d, 0)
      simpa [QuadraticForm.dualProd, hxQ'] using htest
    have hx₂ : x.2 = 0 := Module.eval_apply_injective K (V := W) (by
      simpa using hx₂eval)
    ext <;> simp [hx₁, hx₂]
  · intro hx
    subst x
    simp

variable [FiniteDimensional K V]

/-- Any totally isotropic subspace of `W* × W` has dimension at most `dim(W)`. -/
theorem finrank_le_of_isTotallyIsotropic_dualProd
    {U : Submodule K (Module.Dual K W × W)}
    (hU : (QuadraticForm.dualProd K W).IsTotallyIsotropic U) :
    Module.finrank K U ≤ Module.finrank K W := by
  have hle :
      U ≤ LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    exact (QuadraticMap.associated_isOrtho (Q := QuadraticForm.dualProd K W)).2
      (hU.isOrtho ⟨v, hv⟩ ⟨u, hu⟩)
  have hUorth :
      Module.finrank K U ≤
        Module.finrank K (LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U) :=
    Submodule.finrank_mono hle
  have horth :
      Module.finrank K (LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U) =
        Module.finrank K (Module.Dual K W × W) - Module.finrank K U := by
    simpa using
      (LinearMap.BilinForm.finrank_orthogonal
        ((QuadraticMap.nondegenerate_associated_iff (Q := QuadraticForm.dualProd K W)).2
          (dualProd_nondegenerate (K := K) (V := V) W))
        U)
  have hambient : Module.finrank K (Module.Dual K W × W) = 2 * Module.finrank K W := by
    rw [Module.finrank_prod, Subspace.dual_finrank_eq]
    ring
  have hbound :
      Module.finrank K U ≤ Module.finrank K (Module.Dual K W × W) - Module.finrank K U := by
    rwa [horth] at hUorth
  omega

end HyperbolicWittIndex

variable [FiniteDimensional K V]

/-- An explicitly hyperbolic quadratic space has twice the dimension of the chosen isotropic model. -/
theorem finrank_eq_twice_finrank_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K V = 2 * Module.finrank K W := by
  calc
    Module.finrank K V = Module.finrank K (Module.Dual K W × W) :=
      LinearEquiv.finrank_eq e.toLinearEquiv
    _ = Module.finrank K (Module.Dual K W) + Module.finrank K W := Module.finrank_prod
    _ = 2 * Module.finrank K W := by rw [Subspace.dual_finrank_eq]; ring

/-- In the explicit hyperbolic case, the chosen `⋀W` model has the expected spinor dimension. -/
theorem finrank_isotropicExteriorModel_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K (IsotropicExteriorModel (K := K) W) = 2 ^ (Module.finrank K V / 2) := by
  rw [finrank_isotropicExteriorModel,
    finrank_eq_twice_finrank_of_hyperbolic (K := K) (Q := Q) (W := W) e]
  simp

section HyperbolicWittIndex

variable [Invertible (2 : K)]

/-- Any explicit hyperbolic presentation `Q ≃ dualProd K W` realizes the full Witt index. -/
theorem wittIndex_eq_finrank_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.wittIndex = Module.finrank K W := by
  let splitIsotropic := splitIsotropicSubmodule (K := K) (V := V) W
  have hsplit : (QuadraticForm.dualProd K W).IsTotallyIsotropic splitIsotropic := by
    simpa [splitIsotropic] using splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W
  have hpre :
      Q.IsTotallyIsotropic (splitIsotropic.map e.symm.toLinearMap) := by
    exact hsplit.map e.symm
  have hlower : Module.finrank K W ≤ Q.wittIndex := by
    calc
      Module.finrank K W = Module.finrank K splitIsotropic := by
        simpa [splitIsotropic] using
          (LinearMap.finrank_range_of_inj
            (f := LinearMap.inr K (Module.Dual K W) W)
            LinearMap.inr_injective).symm
      _ = Module.finrank K (splitIsotropic.map e.symm.toLinearMap) := by
        symm
        exact LinearEquiv.finrank_map_eq e.symm.toLinearEquiv splitIsotropic
      _ ≤ Q.wittIndex := Q.finrank_le_wittIndex hpre
  have hmap :
      (QuadraticForm.dualProd K W).IsTotallyIsotropic (Q.wittSubspace.map e.toLinearMap) := by
    intro x
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact (e.map_app y).trans (Q.wittSubspace_isTotallyIsotropic ⟨y, hy⟩)
  have hupper : Q.wittIndex ≤ Module.finrank K W := by
    calc
      Q.wittIndex = Module.finrank K Q.wittSubspace := by rw [Q.finrank_wittSubspace]
      _ = Module.finrank K (Q.wittSubspace.map e.toLinearMap) := by
        symm
        exact LinearEquiv.finrank_map_eq e.toLinearEquiv Q.wittSubspace
      _ ≤ Module.finrank K W :=
        finrank_le_of_isTotallyIsotropic_dualProd (K := K) (V := V) (W := W) hmap
  exact Nat.le_antisymm hupper hlower

/-- The standard split factor `0 × W` realizes the full Witt index of `dualProd K W`. -/
theorem splitIsotropicSubmodule_isMaximalTotallyIsotropic (W : Submodule K V) :
    (QuadraticForm.dualProd K W).IsMaximalTotallyIsotropic
      (splitIsotropicSubmodule (K := K) (V := V) W) := by
  apply QuadraticForm.isMaximalTotallyIsotropic_of_finrank_eq_wittIndex
    (Q := QuadraticForm.dualProd K W)
  · exact splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W
  · apply Nat.le_antisymm
    · exact (QuadraticForm.dualProd K W).finrank_le_wittIndex
        (splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W)
    · calc
        (QuadraticForm.dualProd K W).wittIndex ≤ Module.finrank K W := by
          simpa [QuadraticForm.finrank_wittSubspace] using
            finrank_le_of_isTotallyIsotropic_dualProd
              (K := K) (V := V) (W := W)
              ((QuadraticForm.dualProd K W).wittSubspace_isTotallyIsotropic)
        _ = Module.finrank K (splitIsotropicSubmodule (K := K) (V := V) W) := by
          simpa [splitIsotropicSubmodule] using
            (LinearMap.finrank_range_of_inj
              (f := LinearMap.inr K (Module.Dual K W) W)
              LinearMap.inr_injective).symm

/-- An explicit hyperbolic presentation carries the standard split factor to a maximal isotropic
subspace of the ambient quadratic space. -/
theorem hyperbolicIsotropicSubmodule_isMaximalTotallyIsotropic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.IsMaximalTotallyIsotropic (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) := by
  dsimp [hyperbolicIsotropicSubmodule]
  exact (splitIsotropicSubmodule_isMaximalTotallyIsotropic (K := K) (V := V) W).map e.symm

end HyperbolicWittIndex

/-- An explicitly hyperbolic quadratic space has Witt index `dim(V) / 2`. -/
theorem wittIndex_eq_half_finrank_of_hyperbolic (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Q.wittIndex = Module.finrank K V / 2 := by
  rw [← Q.finrank_wittSubspace,
    finrank_eq_twice_finrank_of_hyperbolic (K := K) (Q := Q) (W := Q.wittSubspace) e]
  omega

/-- In the explicit hyperbolic case, the canonical Witt model has dimension `2 ^ (dim V / 2)`. -/
theorem finrank_wittExteriorModel_of_hyperbolic (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (WittExteriorModel (K := K) Q) = 2 ^ (Module.finrank K V / 2) := by
  rw [finrank_wittExteriorModel, wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e]

section HalfSpinDimensions

variable [Invertible (2 : K)]

/-- In the split hyperbolic case, the even half-spin space has dimension `2^(dim(V)/2 - 1)`. -/
theorem finrank_evenWittExterior_of_hyperbolic (Q : QuadraticForm K V)
    (hQ : 0 < Q.wittIndex)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (evenWittExterior (K := K) Q) = 2 ^ (Module.finrank K V / 2 - 1) := by
  have hW : 0 < Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hQ
  simpa [evenWittExterior, Q.finrank_wittSubspace,
    wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e] using
    finrank_evenExterior (K := K) Q.wittSubspace hW

/-- In the split hyperbolic case, the odd half-spin space has dimension `2^(dim(V)/2 - 1)`. -/
theorem finrank_oddWittExterior_of_hyperbolic (Q : QuadraticForm K V)
    (hQ : 0 < Q.wittIndex)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (oddWittExterior (K := K) Q) = 2 ^ (Module.finrank K V / 2 - 1) := by
  have hW : 0 < Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hQ
  simpa [oddWittExterior, Q.finrank_wittSubspace,
    wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e] using
    finrank_oddExterior (K := K) Q.wittSubspace hW

end HalfSpinDimensions

end HyperbolicDimensions

end Spinor
