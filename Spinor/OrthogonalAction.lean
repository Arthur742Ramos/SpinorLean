/-
  Ambient spin-group action on the underlying quadratic module.
-/

import Spinor.SpinRep
import Mathlib.LinearAlgebra.Determinant

/-!
# Ambient vector representation of the spin group

Ambient vector/isometry action of `spinGroup Q` on the underlying quadratic module `(M, Q)`,
obtained by conjugation on the Clifford copy `ι(Q)(M)`. Each spin element is packaged as a
genuine isometry `Q.IsometryEquiv Q`, and the whole assignment is exposed as a
homomorphism.

This is the covering-map side of the spinor story: together with `Spinor.SpinRep` and the
chosen-model APIs in `Spinor.Presentation`, it lets us formulate the non-factorization of
the spin representation through the isometry representation and, in the split/hyperbolic
setting, identify the kernel as `{1, -1}`.

Also recorded here is a `Group (Q.IsometryEquiv Q)` instance on `QuadraticMap.IsometryEquiv`
together with unfolding lemmas for `one`, `mul`, and `inv`.

## Main declarations

* `QuadraticMap.IsometryEquiv.instGroup` — the group structure on `Q.IsometryEquiv Q`.
* `QuadraticForm.specialOrthogonalGroup` — the determinant-one subgroup of `Q.IsometryEquiv Q`,
  i.e. the packaged special orthogonal target for the covering map.
* `Spinor.cliffordIota_injective`, `Spinor.cliffordAlgebraMap_injective`,
  `Spinor.cliffordIotaRangeEquiv` — the Clifford inclusion of `M` is a linear embedding in
  characteristic not two.
* `Spinor.lipschitzConjAlgEquiv`, `Spinor.pinConjAlgEquiv`, `Spinor.spinConjAlgEquiv` —
  Clifford conjugation by a Lipschitz/pin/spin element as an algebra automorphism.
* `Spinor.lipschitzVectorAction`, `Spinor.lipschitzLinearEquiv`,
  `Spinor.lipschitzLinearRepresentation : lipschitzGroup Q →* (M ≃ₗ[R] M)` — the ambient
  vector action of the Lipschitz group by conjugation on `CliffordAlgebra.ι Q`.
* `Spinor.pinVectorAction`, `Spinor.pinLinearEquiv`,
  `Spinor.pinLinearRepresentation : pinGroup Q →* (M ≃ₗ[R] M)` — the ambient vector action of
  the pin group by conjugation on `CliffordAlgebra.ι Q`.
* `Spinor.spinVectorAction`, `Spinor.spinLinearEquiv`,
  `Spinor.spinLinearRepresentation : spinGroup Q →* (M ≃ₗ[R] M)` — the transported vector
  action of the spin group and its packaging as a linear representation.
* `Spinor.pinVector_preserves_quadratic`, `Spinor.pinIsometryEquiv`,
  `Spinor.pinIsometryRepresentation : pinGroup Q →* Q.IsometryEquiv Q`, together with
  `Spinor.spinVector_preserves_quadratic`, `Spinor.spinIsometryEquiv`,
  `Spinor.spinIsometryRepresentation : spinGroup Q →* Q.IsometryEquiv Q` — each pin/spin
  element acts as an isometry of `Q`, assembled into a homomorphism.
* `Spinor.spinLinearRepresentation_det_eq_one` — over finite-dimensional fields, the ambient spin
  representation has determinant `1`.
* `Spinor.spinSpecialOrthogonalRepresentation`,
  `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional` — the ambient isometry
  representation factors through `QuadraticForm.specialOrthogonalGroup Q`, either from an external
  determinant hypothesis or canonically in the finite-dimensional field setting.
* `Spinor.pinIotaOfQuadraticEqNegOne`, `Spinor.spinIotaPairOfQuadraticEqNegOne`,
  `Spinor.spinSpecialOrthogonalPairGenerator` — canonical pin/spin lifts of norm-`-1` vector
  reflections and their paired special-orthogonal images.
* `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top`
  — surjectivity of the ambient spin covering map reduces to showing those paired generators span
  `SO(V,Q)`.
* `Spinor.spinRepresentation_not_factor_through_isometry_of_kernel_witness`,
  `Spinor.spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one` —
  the spin representation does not factor through the ambient isometry representation when
  a nontrivial scalar kernel element is available.
* `Spinor.iota_mem_pinGroup_of_quadratic_eq_neg_one`,
  `Spinor.neg_one_mem_spinGroup_of_quadratic_eq_neg_one` — a concrete source of such a
  nontrivial scalar element whenever `Q` represents `-1`.
-/

namespace QuadraticMap
namespace IsometryEquiv

variable {R M N : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

@[ext]
theorem ext {Q₁ : QuadraticMap R M N} {Q₂ : QuadraticMap R M N} {f g : Q₁.IsometryEquiv Q₂}
    (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

instance instGroup (Q : QuadraticMap R M N) : Group (Q.IsometryEquiv Q) where
  mul f g := g.trans f
  one := refl Q
  inv f := f.symm
  mul_assoc _ _ _ := by apply DFunLike.ext; intro x; rfl
  mul_one _ := by apply DFunLike.ext; intro x; rfl
  one_mul _ := by apply DFunLike.ext; intro x; rfl
  inv_mul_cancel f := by apply DFunLike.ext; intro x; exact f.symm_apply_apply x

lemma one_eq_refl (Q : QuadraticMap R M N) : (1 : Q.IsometryEquiv Q) = refl Q := rfl
lemma mul_eq_trans {Q : QuadraticMap R M N} (f g : Q.IsometryEquiv Q) : f * g = g.trans f := rfl

@[simp]
lemma coe_one (Q : QuadraticMap R M N) : ⇑(1 : Q.IsometryEquiv Q) = id := rfl

@[simp]
lemma coe_inv {Q : QuadraticMap R M N} (f : Q.IsometryEquiv Q) : ⇑f⁻¹ = ⇑f.symm := rfl

@[simp]
lemma one_apply (Q : QuadraticMap R M N) (x : M) : (1 : Q.IsometryEquiv Q) x = x := rfl

@[simp]
lemma mul_apply {Q : QuadraticMap R M N} (f g : Q.IsometryEquiv Q) (x : M) :
    (f * g) x = f (g x) := rfl

@[simp]
lemma toLinearEquiv_one (Q : QuadraticMap R M N) :
    ((1 : Q.IsometryEquiv Q) : M ≃ₗ[R] M) = LinearEquiv.refl R M := rfl

@[simp]
lemma toLinearEquiv_mul {Q : QuadraticMap R M N} (f g : Q.IsometryEquiv Q) :
    ((f * g : Q.IsometryEquiv Q) : M ≃ₗ[R] M) = (f : M ≃ₗ[R] M) * (g : M ≃ₗ[R] M) := rfl

@[simp]
lemma toLinearEquiv_inv {Q : QuadraticMap R M N} (f : Q.IsometryEquiv Q) :
    ((f⁻¹ : Q.IsometryEquiv Q) : M ≃ₗ[R] M) = (f : M ≃ₗ[R] M)⁻¹ := rfl

end IsometryEquiv
end QuadraticMap

namespace QuadraticForm

variable {R M : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- The determinant-one subgroup of the ambient isometry group of `Q`. This packages the special
orthogonal target for the spin covering map while staying in the ambient `Q.IsometryEquiv Q`
language. -/
def specialOrthogonalGroup (Q : QuadraticForm R M) : Subgroup (Q.IsometryEquiv Q) where
  carrier := {f | LinearEquiv.det (f : M ≃ₗ[R] M) = 1}
  one_mem' := by
    simp [QuadraticMap.IsometryEquiv.toLinearEquiv_one]
  mul_mem' {f} {g} hf hg := by
    have hf' : LinearEquiv.det (f : M ≃ₗ[R] M) = 1 := hf
    have hg' : LinearEquiv.det (g : M ≃ₗ[R] M) = 1 := hg
    have hmul :
        LinearEquiv.det ((f : M ≃ₗ[R] M) * (g : M ≃ₗ[R] M)) =
          LinearEquiv.det (f : M ≃ₗ[R] M) * LinearEquiv.det (g : M ≃ₗ[R] M) :=
      map_mul (LinearEquiv.det : (M ≃ₗ[R] M) →* Rˣ) (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M)
    calc
      LinearEquiv.det ((f * g : Q.IsometryEquiv Q) : M ≃ₗ[R] M) =
          LinearEquiv.det (f : M ≃ₗ[R] M) * LinearEquiv.det (g : M ≃ₗ[R] M) := by
            rw [QuadraticMap.IsometryEquiv.toLinearEquiv_mul]
            exact hmul
      _ = 1 := by
            rw [hf', hg']
            simp
  inv_mem' {f} hf := by
    have hf' : LinearEquiv.det (f : M ≃ₗ[R] M) = 1 := hf
    calc
      LinearEquiv.det ((f⁻¹ : Q.IsometryEquiv Q) : M ≃ₗ[R] M) =
          (LinearEquiv.det (f : M ≃ₗ[R] M))⁻¹ := by
            rw [QuadraticMap.IsometryEquiv.toLinearEquiv_inv]
            exact map_inv (LinearEquiv.det : (M ≃ₗ[R] M) →* Rˣ) (f : M ≃ₗ[R] M)
      _ = 1 := by
            rw [hf']
            simp

omit [Module.Free R M] [Module.Finite R M] in
@[simp]
theorem mem_specialOrthogonalGroup_iff (Q : QuadraticForm R M) (f : Q.IsometryEquiv Q) :
    f ∈ Q.specialOrthogonalGroup ↔ LinearEquiv.det (f : M ≃ₗ[R] M) = 1 :=
  Iff.rfl

omit [Module.Free R M] [Module.Finite R M] in
@[simp]
theorem det_eq_one (Q : QuadraticForm R M) (f : Q.specialOrthogonalGroup) :
    LinearEquiv.det ((f : Q.IsometryEquiv Q) : M ≃ₗ[R] M) = 1 :=
  f.2

end QuadraticForm

namespace Spinor

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- In characteristic not two, the Clifford inclusion of vectors is injective. -/
theorem cliffordIota_injective : Function.Injective (CliffordAlgebra.ι Q) := by
  intro m₁ m₂ h
  have h' : ExteriorAlgebra.ι R m₁ = ExteriorAlgebra.ι R m₂ := by
    simpa [CliffordAlgebra.equivExterior] using congrArg (CliffordAlgebra.equivExterior Q) h
  exact (ExteriorAlgebra.ι_inj R _ _).mp h'

/-- In characteristic not two, scalars embed faithfully into the Clifford algebra. -/
theorem cliffordAlgebraMap_injective : Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s h
  have h' : algebraMap R (ExteriorAlgebra R M) r = algebraMap R (ExteriorAlgebra R M) s := by
    simpa [CliffordAlgebra.equivExterior] using congrArg (CliffordAlgebra.equivExterior Q) h
  exact (ExteriorAlgebra.algebraMap_leftInverse (R := R) M).injective h'

/-- The Clifford inclusion identifies the ambient module with its image inside `CliffordAlgebra Q`. -/
noncomputable def cliffordIotaRangeEquiv :
    M ≃ₗ[R] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (cliffordIota_injective (Q := Q))

@[simp]
theorem cliffordIotaRangeEquiv_apply (m : M) :
    ((cliffordIotaRangeEquiv (Q := Q)) m : CliffordAlgebra Q) = CliffordAlgebra.ι Q m := rfl

@[simp]
theorem cliffordIotaRangeEquiv_symm_apply (x : LinearMap.range (CliffordAlgebra.ι Q)) :
    CliffordAlgebra.ι Q ((cliffordIotaRangeEquiv (Q := Q)).symm x) = x := by
  exact congrArg Subtype.val ((cliffordIotaRangeEquiv (Q := Q)).apply_symm_apply x)

/-- The natural inclusion `Spin(Q) → Pin(Q)`. -/
noncomputable def spinGroupToPinGroup : spinGroup Q →* pinGroup Q where
  toFun x := ⟨x, spinGroup.mem_pin x.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Invertible (2 : R)] in
@[simp]
theorem coe_spinGroupToPinGroup (x : spinGroup Q) :
    ((spinGroupToPinGroup (Q := Q) x : pinGroup Q) : CliffordAlgebra Q) = x := rfl

/-- Conjugation by a Lipschitz element as an algebra automorphism of the Clifford algebra. -/
noncomputable def lipschitzConjAlgEquiv (x : lipschitzGroup Q) :
    CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv R (CliffordAlgebra Q)
    (ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ))

omit [Invertible (2 : R)] in
@[simp]
theorem lipschitzConjAlgEquiv_apply (x : lipschitzGroup Q) (a : CliffordAlgebra Q) :
    lipschitzConjAlgEquiv (Q := Q) x a =
      ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) • a := rfl

/-- The Lipschitz conjugation action preserves the Clifford copy of the ambient vector space. -/
noncomputable def lipschitzRangeAction (x : lipschitzGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) →ₗ[R] LinearMap.range (CliffordAlgebra.ι Q) where
  toFun y := by
    let z := lipschitzConjAlgEquiv (Q := Q) x y
    refine ⟨z, ?_⟩
    let m : M := Classical.choose y.property
    have hm : CliffordAlgebra.ι Q m = (y : CliffordAlgebra Q) := Classical.choose_spec y.property
    exact by
      simpa [z, hm] using lipschitzGroup.conjAct_smul_ι_mem_range_ι
        (Q := Q) (x := (x : (CliffordAlgebra Q)ˣ)) x.property m
  map_add' y z := by
    apply Subtype.ext
    simp [lipschitzConjAlgEquiv]
  map_smul' a y := by
    apply Subtype.ext
    simp [lipschitzConjAlgEquiv]

@[simp]
theorem lipschitzRangeAction_apply (x : lipschitzGroup Q)
    (y : LinearMap.range (CliffordAlgebra.ι Q)) :
    ((lipschitzRangeAction (Q := Q) x y : LinearMap.range (CliffordAlgebra.ι Q)) :
        CliffordAlgebra Q) =
      lipschitzConjAlgEquiv (Q := Q) x y := rfl

/-- The ambient linear map induced by Lipschitz conjugation on the image of `CliffordAlgebra.ι`. -/
noncomputable def lipschitzVectorAction (x : lipschitzGroup Q) : M →ₗ[R] M :=
  (cliffordIotaRangeEquiv (Q := Q)).symm.toLinearMap.comp
    ((lipschitzRangeAction (Q := Q) x).comp (cliffordIotaRangeEquiv (Q := Q)).toLinearMap)

@[simp]
theorem lipschitzVectorAction_ι (x : lipschitzGroup Q) (m : M) :
    CliffordAlgebra.ι Q (lipschitzVectorAction (Q := Q) x m) =
      ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) • CliffordAlgebra.ι Q m := by
  simp [lipschitzVectorAction, lipschitzConjAlgEquiv]

/-- Each Lipschitz element acts by a linear automorphism of the ambient quadratic module. -/
noncomputable def lipschitzLinearEquiv (x : lipschitzGroup Q) : M ≃ₗ[R] M :=
  { lipschitzVectorAction (Q := Q) x with
    invFun := lipschitzVectorAction (Q := Q) x⁻¹
    left_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [lipschitzVectorAction_ι]
    right_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [lipschitzVectorAction_ι] }

@[simp]
theorem lipschitzLinearEquiv_apply (x : lipschitzGroup Q) (m : M) :
    lipschitzLinearEquiv (Q := Q) x m = lipschitzVectorAction (Q := Q) x m := rfl

@[simp]
theorem lipschitzLinearEquiv_ι (x : lipschitzGroup Q) (m : M) :
    CliffordAlgebra.ι Q (lipschitzLinearEquiv (Q := Q) x m) =
      ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) • CliffordAlgebra.ι Q m :=
  lipschitzVectorAction_ι (Q := Q) x m

/-- The ambient vector action of the Lipschitz group. -/
noncomputable def lipschitzLinearRepresentation : lipschitzGroup Q →* (M ≃ₗ[R] M) where
  toFun := lipschitzLinearEquiv (Q := Q)
  map_one' := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp
  map_mul' x y := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp [LinearEquiv.mul_apply, mul_smul]

@[simp]
theorem lipschitzLinearRepresentation_apply (x : lipschitzGroup Q) :
    lipschitzLinearRepresentation (Q := Q) x = lipschitzLinearEquiv (Q := Q) x := rfl

/-- Conjugation by a pin element as an algebra automorphism of the Clifford algebra. -/
noncomputable def pinConjAlgEquiv (x : pinGroup Q) : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv R (CliffordAlgebra Q) (ConjAct.toConjAct (pinGroup.toUnits x))

omit [Invertible (2 : R)] in
@[simp]
theorem pinConjAlgEquiv_apply (x : pinGroup Q) (a : CliffordAlgebra Q) :
    pinConjAlgEquiv (Q := Q) x a =
      ConjAct.toConjAct (pinGroup.toUnits x) • a := rfl

/-- The pin conjugation action preserves the Clifford copy of the ambient vector space. -/
noncomputable def pinRangeAction (x : pinGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) →ₗ[R] LinearMap.range (CliffordAlgebra.ι Q) where
  toFun y := by
    let z := pinConjAlgEquiv (Q := Q) x y
    refine ⟨z, ?_⟩
    let m : M := Classical.choose y.property
    have hm : CliffordAlgebra.ι Q m = (y : CliffordAlgebra Q) := Classical.choose_spec y.property
    exact by
      simpa [z, hm] using pinGroup.conjAct_smul_ι_mem_range_ι
        (Q := Q) (x := pinGroup.toUnits x) x.prop m
  map_add' y z := by
    apply Subtype.ext
    simp [pinConjAlgEquiv]
  map_smul' a y := by
    apply Subtype.ext
    simp [pinConjAlgEquiv]

@[simp]
theorem pinRangeAction_apply (x : pinGroup Q) (y : LinearMap.range (CliffordAlgebra.ι Q)) :
    ((pinRangeAction (Q := Q) x y : LinearMap.range (CliffordAlgebra.ι Q)) : CliffordAlgebra Q) =
      pinConjAlgEquiv (Q := Q) x y := rfl

/-- The ambient linear map induced by pin conjugation on the image of `CliffordAlgebra.ι`. -/
noncomputable def pinVectorAction (x : pinGroup Q) : M →ₗ[R] M :=
  (cliffordIotaRangeEquiv (Q := Q)).symm.toLinearMap.comp
    ((pinRangeAction (Q := Q) x).comp (cliffordIotaRangeEquiv (Q := Q)).toLinearMap)

@[simp]
theorem pinVectorAction_ι (x : pinGroup Q) (m : M) :
    CliffordAlgebra.ι Q (pinVectorAction (Q := Q) x m) =
      ConjAct.toConjAct (pinGroup.toUnits x) • CliffordAlgebra.ι Q m := by
  simp [pinVectorAction, pinConjAlgEquiv]

/-- Each pin element acts by a linear automorphism of the ambient quadratic module. -/
noncomputable def pinLinearEquiv (x : pinGroup Q) : M ≃ₗ[R] M :=
  { pinVectorAction (Q := Q) x with
    invFun := pinVectorAction (Q := Q) x⁻¹
    left_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [pinVectorAction_ι]
    right_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [pinVectorAction_ι] }

@[simp]
theorem pinLinearEquiv_apply (x : pinGroup Q) (m : M) :
    pinLinearEquiv (Q := Q) x m = pinVectorAction (Q := Q) x m := rfl

@[simp]
theorem pinLinearEquiv_ι (x : pinGroup Q) (m : M) :
    CliffordAlgebra.ι Q (pinLinearEquiv (Q := Q) x m) =
      ConjAct.toConjAct (pinGroup.toUnits x) • CliffordAlgebra.ι Q m :=
  pinVectorAction_ι (Q := Q) x m

/-- The ambient vector action of the pin group. -/
noncomputable def pinLinearRepresentation : pinGroup Q →* (M ≃ₗ[R] M) where
  toFun := pinLinearEquiv (Q := Q)
  map_one' := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp
  map_mul' x y := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp [LinearEquiv.mul_apply, mul_smul]

@[simp]
theorem pinLinearRepresentation_apply (x : pinGroup Q) :
    pinLinearRepresentation (Q := Q) x = pinLinearEquiv (Q := Q) x := rfl

/-- Scalar pin elements act trivially on the ambient linear representation. -/
theorem pinLinearRepresentation_eq_one_of_coe_eq_algebraMap (x : pinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    pinLinearRepresentation (Q := Q) x = 1 := by
  ext m
  show pinLinearRepresentation (Q := Q) x m = m
  apply cliffordIota_injective (Q := Q)
  have hx' : (((pinGroup.toUnits x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      algebraMap R (CliffordAlgebra Q) r := by
    simpa using hx
  rw [pinLinearRepresentation_apply, pinLinearEquiv_ι, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct]
  rw [hx', Algebra.commutes r (CliffordAlgebra.ι Q m), mul_assoc, ← hx']
  have hmul : (x : CliffordAlgebra Q) * ↑x⁻¹ = (1 : CliffordAlgebra Q) := by
    simpa [pinGroup.star_eq_inv] using (pinGroup.coe_mul_star_self (Q := Q) x)
  have hmul' :
      (((pinGroup.toUnits x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ↑((pinGroup.toUnits x)⁻¹)) = (1 : CliffordAlgebra Q) := by
    simpa using hmul
  rw [hmul', mul_one]

noncomputable instance : MulAction (pinGroup Q) M :=
  MulAction.compHom M (pinLinearRepresentation (Q := Q))

@[simp]
theorem pinVector_smul_def (x : pinGroup Q) (m : M) :
    x • m = pinLinearRepresentation (Q := Q) x m := rfl

/-- Pin conjugation preserves the ambient quadratic form. -/
theorem pinVector_preserves_quadratic (x : pinGroup Q) (m : M) :
    Q (pinLinearRepresentation (Q := Q) x m) = Q m := by
  have hsquare :
      CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) =
        algebraMap R (CliffordAlgebra Q) (Q m) := by
    calc
      CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) =
          pinConjAlgEquiv (Q := Q) x (CliffordAlgebra.ι Q m) *
            pinConjAlgEquiv (Q := Q) x (CliffordAlgebra.ι Q m) := by
              rw [pinLinearRepresentation_apply, pinLinearEquiv_ι (Q := Q) x m]
              simp [pinConjAlgEquiv]
      _ = pinConjAlgEquiv (Q := Q) x
            (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m) := by
              symm
              exact (pinConjAlgEquiv (Q := Q) x).map_mul _ _
      _ = pinConjAlgEquiv (Q := Q) x (algebraMap R (CliffordAlgebra Q) (Q m)) := by
              rw [CliffordAlgebra.ι_sq_scalar (Q := Q)]
      _ = algebraMap R (CliffordAlgebra Q) (Q m) := by
              simp [pinConjAlgEquiv]
  have hsquare' :
      CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (pinLinearRepresentation (Q := Q) x m) =
        algebraMap R (CliffordAlgebra Q) (Q (pinLinearRepresentation (Q := Q) x m)) :=
    CliffordAlgebra.ι_sq_scalar (Q := Q) _
  apply cliffordAlgebraMap_injective (Q := Q)
  exact hsquare'.symm.trans hsquare

/-- Each pin element acts by an isometry of the ambient quadratic form. -/
noncomputable def pinIsometryEquiv (x : pinGroup Q) : Q.IsometryEquiv Q where
  toLinearEquiv := pinLinearRepresentation (Q := Q) x
  map_app' := pinVector_preserves_quadratic (Q := Q) x

@[simp]
theorem pinIsometryEquiv_apply (x : pinGroup Q) (m : M) :
    pinIsometryEquiv (Q := Q) x m = pinLinearRepresentation (Q := Q) x m := rfl

/-- The ambient pin action packaged directly as a homomorphism into quadratic-form isometries. -/
noncomputable def pinIsometryRepresentation : pinGroup Q →* Q.IsometryEquiv Q where
  toFun := pinIsometryEquiv (Q := Q)
  map_one' := by
    apply DFunLike.ext
    intro m
    simpa [pinIsometryEquiv_apply] using
      congrArg (fun e : M ≃ₗ[R] M => e m) (pinLinearRepresentation (Q := Q)).map_one
  map_mul' x y := by
    apply DFunLike.ext
    intro m
    simpa [pinIsometryEquiv_apply, QuadraticMap.IsometryEquiv.mul_apply, LinearEquiv.mul_apply] using
      congrArg (fun e : M ≃ₗ[R] M => e m) ((pinLinearRepresentation (Q := Q)).map_mul x y)

@[simp]
theorem pinIsometryRepresentation_apply (x : pinGroup Q) :
    pinIsometryRepresentation (Q := Q) x = pinIsometryEquiv (Q := Q) x := rfl

@[simp]
theorem pinIsometryRepresentation_toLinearEquiv (x : pinGroup Q) :
    ((pinIsometryRepresentation (Q := Q) x : Q.IsometryEquiv Q) : M ≃ₗ[R] M) =
      pinLinearRepresentation (Q := Q) x := rfl

/-- Conjugation by a spin element as an algebra automorphism of the Clifford algebra. -/
noncomputable def spinConjAlgEquiv (x : spinGroup Q) : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv R (CliffordAlgebra Q) (ConjAct.toConjAct (spinGroup.toUnits x))

omit [Invertible (2 : R)] in
@[simp]
theorem spinConjAlgEquiv_apply (x : spinGroup Q) (a : CliffordAlgebra Q) :
    spinConjAlgEquiv (Q := Q) x a =
      ConjAct.toConjAct (spinGroup.toUnits x) • a := rfl

/-- The spin conjugation action preserves the Clifford copy of the ambient vector space. -/
noncomputable def spinRangeAction (x : spinGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) →ₗ[R] LinearMap.range (CliffordAlgebra.ι Q) where
  toFun y := by
    let z := spinConjAlgEquiv (Q := Q) x y
    refine ⟨z, ?_⟩
    let m : M := Classical.choose y.property
    have hm : CliffordAlgebra.ι Q m = (y : CliffordAlgebra Q) := Classical.choose_spec y.property
    exact by
      simpa [z, hm] using spinGroup.conjAct_smul_ι_mem_range_ι
        (Q := Q) (x := spinGroup.toUnits x) x.prop m
  map_add' y z := by
    apply Subtype.ext
    simp [spinConjAlgEquiv]
  map_smul' a y := by
    apply Subtype.ext
    simp [spinConjAlgEquiv]

@[simp]
theorem spinRangeAction_apply (x : spinGroup Q) (y : LinearMap.range (CliffordAlgebra.ι Q)) :
    ((spinRangeAction (Q := Q) x y : LinearMap.range (CliffordAlgebra.ι Q)) : CliffordAlgebra Q) =
      spinConjAlgEquiv (Q := Q) x y := rfl

/-- The ambient linear map induced by spin conjugation on the image of `CliffordAlgebra.ι`. -/
noncomputable def spinVectorAction (x : spinGroup Q) : M →ₗ[R] M :=
  (cliffordIotaRangeEquiv (Q := Q)).symm.toLinearMap.comp
    ((spinRangeAction (Q := Q) x).comp (cliffordIotaRangeEquiv (Q := Q)).toLinearMap)

@[simp]
theorem spinVectorAction_ι (x : spinGroup Q) (m : M) :
    CliffordAlgebra.ι Q (spinVectorAction (Q := Q) x m) =
      ConjAct.toConjAct (spinGroup.toUnits x) • CliffordAlgebra.ι Q m := by
  simp [spinVectorAction, spinConjAlgEquiv]

/-- Each spin element acts by a linear automorphism of the ambient quadratic module. -/
noncomputable def spinLinearEquiv (x : spinGroup Q) : M ≃ₗ[R] M :=
  { spinVectorAction (Q := Q) x with
    invFun := spinVectorAction (Q := Q) x⁻¹
    left_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [spinVectorAction_ι]
    right_inv := by
      intro m
      apply cliffordIota_injective (Q := Q)
      simp [spinVectorAction_ι] }

@[simp]
theorem spinLinearEquiv_apply (x : spinGroup Q) (m : M) :
    spinLinearEquiv (Q := Q) x m = spinVectorAction (Q := Q) x m := rfl

@[simp]
theorem spinLinearEquiv_ι (x : spinGroup Q) (m : M) :
    CliffordAlgebra.ι Q (spinLinearEquiv (Q := Q) x m) =
      ConjAct.toConjAct (spinGroup.toUnits x) • CliffordAlgebra.ι Q m :=
  spinVectorAction_ι (Q := Q) x m

/-- The ambient vector action of the spin group. -/
noncomputable def spinLinearRepresentation : spinGroup Q →* (M ≃ₗ[R] M) where
  toFun := spinLinearEquiv (Q := Q)
  map_one' := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp
  map_mul' x y := by
    ext m
    apply cliffordIota_injective (Q := Q)
    simp [LinearEquiv.mul_apply, mul_smul]

@[simp]
theorem spinLinearRepresentation_apply (x : spinGroup Q) :
    spinLinearRepresentation (Q := Q) x = spinLinearEquiv (Q := Q) x := rfl

/-- Scalar spin elements act trivially on the ambient linear representation. -/
theorem spinLinearRepresentation_eq_one_of_coe_eq_algebraMap (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    spinLinearRepresentation (Q := Q) x = 1 := by
  ext m
  show spinLinearRepresentation (Q := Q) x m = m
  apply cliffordIota_injective (Q := Q)
  have hx' : (((spinGroup.toUnits x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      algebraMap R (CliffordAlgebra Q) r := by
    simpa using hx
  rw [spinLinearRepresentation_apply, spinLinearEquiv_ι, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct]
  rw [hx', Algebra.commutes r (CliffordAlgebra.ι Q m), mul_assoc, ← hx']
  have hmul : (x : CliffordAlgebra Q) * ↑x⁻¹ = (1 : CliffordAlgebra Q) := by
    simpa [spinGroup.star_eq_inv] using (spinGroup.coe_mul_star_self (Q := Q) x)
  have hmul' :
      (((spinGroup.toUnits x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ↑((spinGroup.toUnits x)⁻¹)) = (1 : CliffordAlgebra Q) := by
    simpa using hmul
  rw [hmul', mul_one]

noncomputable instance : MulAction (spinGroup Q) M :=
  MulAction.compHom M (spinLinearRepresentation (Q := Q))

@[simp]
theorem spinVector_smul_def (x : spinGroup Q) (m : M) :
    x • m = spinLinearRepresentation (Q := Q) x m := rfl

/-- Spin conjugation preserves the ambient quadratic form. -/
theorem spinVector_preserves_quadratic (x : spinGroup Q) (m : M) :
    Q (spinLinearRepresentation (Q := Q) x m) = Q m := by
  have hsquare :
      CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) =
        algebraMap R (CliffordAlgebra Q) (Q m) := by
    calc
      CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) =
          spinConjAlgEquiv (Q := Q) x (CliffordAlgebra.ι Q m) *
            spinConjAlgEquiv (Q := Q) x (CliffordAlgebra.ι Q m) := by
              rw [spinLinearRepresentation_apply, spinLinearEquiv_ι (Q := Q) x m]
              simp [spinConjAlgEquiv]
      _ = spinConjAlgEquiv (Q := Q) x
            (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m) := by
              symm
              exact (spinConjAlgEquiv (Q := Q) x).map_mul _ _
      _ = spinConjAlgEquiv (Q := Q) x (algebraMap R (CliffordAlgebra Q) (Q m)) := by
              rw [CliffordAlgebra.ι_sq_scalar (Q := Q)]
      _ = algebraMap R (CliffordAlgebra Q) (Q m) := by
              simp [spinConjAlgEquiv]
  have hsquare' :
      CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) *
          CliffordAlgebra.ι Q (spinLinearRepresentation (Q := Q) x m) =
        algebraMap R (CliffordAlgebra Q) (Q (spinLinearRepresentation (Q := Q) x m)) :=
    CliffordAlgebra.ι_sq_scalar (Q := Q) _
  apply cliffordAlgebraMap_injective (Q := Q)
  exact hsquare'.symm.trans hsquare

/-- Each spin element acts by an isometry of the ambient quadratic form. -/
noncomputable def spinIsometryEquiv (x : spinGroup Q) : Q.IsometryEquiv Q where
  toLinearEquiv := spinLinearRepresentation (Q := Q) x
  map_app' := spinVector_preserves_quadratic (Q := Q) x

@[simp]
theorem spinIsometryEquiv_apply (x : spinGroup Q) (m : M) :
    spinIsometryEquiv (Q := Q) x m = spinLinearRepresentation (Q := Q) x m := rfl

/-- The ambient spin action packaged directly as a homomorphism into quadratic-form isometries. -/
noncomputable def spinIsometryRepresentation : spinGroup Q →* Q.IsometryEquiv Q where
  toFun := spinIsometryEquiv (Q := Q)
  map_one' := by
    apply DFunLike.ext
    intro m
    simpa [spinIsometryEquiv_apply] using
      congrArg (fun e : M ≃ₗ[R] M => e m) (spinLinearRepresentation (Q := Q)).map_one
  map_mul' x y := by
    apply DFunLike.ext
    intro m
    simpa [spinIsometryEquiv_apply, QuadraticMap.IsometryEquiv.mul_apply, LinearEquiv.mul_apply] using
      congrArg (fun e : M ≃ₗ[R] M => e m) ((spinLinearRepresentation (Q := Q)).map_mul x y)

@[simp]
theorem spinIsometryRepresentation_apply (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = spinIsometryEquiv (Q := Q) x := rfl

@[simp]
theorem spinIsometryRepresentation_toLinearEquiv (x : spinGroup Q) :
    ((spinIsometryRepresentation (Q := Q) x : Q.IsometryEquiv Q) : M ≃ₗ[R] M) =
      spinLinearRepresentation (Q := Q) x := rfl

@[simp]
theorem pinLinearRepresentation_spinGroupToPinGroup (x : spinGroup Q) :
    pinLinearRepresentation (Q := Q) (spinGroupToPinGroup (Q := Q) x) =
      spinLinearRepresentation (Q := Q) x := by
  ext m
  apply cliffordIota_injective (Q := Q)
  have hUnits : pinGroup.toUnits (spinGroupToPinGroup (Q := Q) x) = spinGroup.toUnits x := by
    ext
    rfl
  rw [pinLinearRepresentation_apply, spinLinearRepresentation_apply,
    pinLinearEquiv_ι, spinLinearEquiv_ι, hUnits]

@[simp]
theorem lipschitzLinearRepresentation_toUnits_spinGroup (x : spinGroup Q) :
    lipschitzLinearRepresentation (Q := Q)
        ⟨spinGroup.toUnits x, spinGroup.units_mem_lipschitzGroup x.prop⟩ =
      spinLinearRepresentation (Q := Q) x := by
  ext m
  apply cliffordIota_injective (Q := Q)
  simp

@[simp]
theorem pinIsometryRepresentation_comp_spinGroupToPinGroup :
    (pinIsometryRepresentation (Q := Q)).comp (spinGroupToPinGroup (Q := Q)) =
      spinIsometryRepresentation (Q := Q) := by
  ext x m
  exact congrArg (fun e : M ≃ₗ[R] M => e m)
    (pinLinearRepresentation_spinGroupToPinGroup (Q := Q) x)

section SpecialOrthogonal

/-- Once the determinant-one step is established, the ambient spin-to-isometry map factors through
the packaged special orthogonal subgroup. This isolates the remaining determinant/surjectivity gap
in the roadmap's double-cover statement. -/
noncomputable def spinSpecialOrthogonalRepresentation
    [Module.Free R M] [Module.Finite R M]
    (hdet : ∀ x : spinGroup Q, LinearEquiv.det (spinLinearRepresentation (Q := Q) x) = 1) :
    spinGroup Q →* Q.specialOrthogonalGroup where
  toFun x := ⟨spinIsometryRepresentation (Q := Q) x,
    by
      simpa [QuadraticForm.mem_specialOrthogonalGroup_iff, spinIsometryRepresentation_toLinearEquiv]
        using hdet x⟩
  map_one' := by
    apply Subtype.ext
    exact (spinIsometryRepresentation (Q := Q)).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (spinIsometryRepresentation (Q := Q)).map_mul x y

@[simp]
theorem coe_spinSpecialOrthogonalRepresentation
    [Module.Free R M] [Module.Finite R M]
    (hdet : ∀ x : spinGroup Q, LinearEquiv.det (spinLinearRepresentation (Q := Q) x) = 1)
    (x : spinGroup Q) :
    ↑(spinSpecialOrthogonalRepresentation (Q := Q) hdet x) =
      spinIsometryRepresentation (Q := Q) x := rfl

@[simp]
theorem spinSpecialOrthogonalRepresentation_comp_subtype
    [Module.Free R M] [Module.Finite R M]
    (hdet : ∀ x : spinGroup Q, LinearEquiv.det (spinLinearRepresentation (Q := Q) x) = 1) :
    (Q.specialOrthogonalGroup.subtype).comp
        (spinSpecialOrthogonalRepresentation (Q := Q) hdet) =
      spinIsometryRepresentation (Q := Q) := by
  ext x
  rfl

end SpecialOrthogonal

/-- Scalar spin elements act trivially on the ambient quadratic-form isometry representation. -/
theorem spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    spinIsometryRepresentation (Q := Q) x = 1 := by
  ext m
  simpa [spinIsometryRepresentation_apply] using
    congrArg (fun e : M ≃ₗ[R] M => e m)
      (spinLinearRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x r hx)

/-- A kernel element acts trivially on the full Clifford algebra by conjugation. -/
theorem spinConjAlgEquiv_eq_refl_of_spinIsometryRepresentation_eq_one (x : spinGroup Q)
    (hx : spinIsometryRepresentation (Q := Q) x = 1) :
    spinConjAlgEquiv (Q := Q) x = AlgEquiv.refl := by
  ext a
  have hhom :
      (spinConjAlgEquiv (Q := Q) x).toAlgHom =
        (AlgEquiv.refl : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q).toAlgHom := by
    refine CliffordAlgebra.hom_ext ?_
    ext m
    have hm : spinLinearEquiv (Q := Q) x m = m := by
      simpa [spinIsometryRepresentation_apply, spinIsometryEquiv_apply,
        spinLinearRepresentation_apply] using
        congrArg (fun e : Q.IsometryEquiv Q => e m) hx
    simpa [spinConjAlgEquiv_apply, hm] using (spinLinearEquiv_ι (Q := Q) x m).symm
  exact congrArg (fun f : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q => f a) hhom

/-- A kernel element commutes with every Clifford element. -/
theorem commute_of_spinIsometryRepresentation_eq_one (x : spinGroup Q)
    (hx : spinIsometryRepresentation (Q := Q) x = 1) (a : CliffordAlgebra Q) :
    Commute (x : CliffordAlgebra Q) a := by
  let u : (CliffordAlgebra Q)ˣ := spinGroup.toUnits x
  have hconj : spinConjAlgEquiv (Q := Q) x a = a := by
    simp [spinConjAlgEquiv_eq_refl_of_spinIsometryRepresentation_eq_one (Q := Q) x hx]
  have hcomm :
      (u : CliffordAlgebra Q) * a = a * (u : CliffordAlgebra Q) := by
    have hconj' : (u : CliffordAlgebra Q) * a * ↑u⁻¹ = a := by
      simpa [u, spinConjAlgEquiv_apply, ConjAct.toConjAct_smul] using hconj
    rw [Units.mul_inv_eq_iff_eq_mul] at hconj'
    exact hconj'
  simpa [u, Commute] using hcomm

/-- A scalar spin element has square `1` in the base ring. -/
theorem scalar_sq_eq_one_of_coe_eq_algebraMap (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    r * r = 1 := by
  apply (cliffordAlgebraMap_injective (Q := Q))
  calc
    algebraMap R (CliffordAlgebra Q) (r * r) =
        algebraMap R (CliffordAlgebra Q) r * algebraMap R (CliffordAlgebra Q) r := by
          rw [map_mul]
    _ = star (algebraMap R (CliffordAlgebra Q) r) * algebraMap R (CliffordAlgebra Q) r := by
          rw [CliffordAlgebra.star_algebraMap]
    _ = star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) := by rw [hx]
    _ = algebraMap R (CliffordAlgebra Q) 1 := by
          exact spinGroup.coe_star_mul_self x

/-- Over a domain, a scalar spin element must be `±1`. -/
theorem scalar_eq_one_or_neg_one_of_coe_eq_algebraMap [NoZeroDivisors R] (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    r = 1 ∨ r = -1 := by
  have hrsq : r * r = 1 :=
    scalar_sq_eq_one_of_coe_eq_algebraMap (Q := Q) x r hx
  have hfac : (r + 1) * (r - 1) = 0 := by
    rw [← (Commute.all r (1 : R)).mul_self_sub_mul_self_eq]
    simp [hrsq]
  rcases mul_eq_zero.mp hfac with hplus | hminus
  · right
    exact eq_neg_iff_add_eq_zero.mpr hplus
  · left
    exact sub_eq_zero.mp hminus

/-- Over a domain, a scalar spin element has underlying Clifford value `1` or `-1`. -/
theorem coe_eq_one_or_neg_one_of_coe_eq_algebraMap [NoZeroDivisors R] (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  rcases scalar_eq_one_or_neg_one_of_coe_eq_algebraMap (Q := Q) x r hx with hr | hr
  · left
    simpa [hr] using hx
  · right
    simpa [hr] using hx

/-- Over a domain, the scalar part of the kernel of the ambient isometry representation is exactly
`{1, -1}`. -/
theorem spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_coe_eq_algebraMap
    [NoZeroDivisors R] (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  constructor
  · intro _
    exact coe_eq_one_or_neg_one_of_coe_eq_algebraMap (Q := Q) x r hx
  · intro h
    rcases h with h1 | hneg
    · simpa using
        spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x 1 (by simpa using h1)
    · simpa using
        spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x (-1)
          (by simpa using hneg)

/-- Once one knows that every kernel element is scalar, the ambient isometry kernel is exactly
`{1, -1}` over a domain. This isolates the remaining central/scalar step in the full double-cover
theorem. -/
theorem spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_kernel_scalars
    [NoZeroDivisors R]
    (hscalar : ∀ x : spinGroup Q, spinIsometryRepresentation (Q := Q) x = 1 →
      ∃ r, (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r)
    (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  constructor
  · intro hker
    rcases hscalar x hker with ⟨r, hr⟩
    exact (spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_coe_eq_algebraMap
      (Q := Q) x r hr).mp hker
  · intro h
    rcases h with h1 | hneg
    · simpa using
        spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x 1 (by simpa using h1)
    · simpa using
        spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x (-1)
          (by simpa using hneg)

/-- Any kernel witness with nontrivial spinor action obstructs factorization of the spin
representation through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_kernel_witness (x : spinGroup Q)
    (hker : spinIsometryRepresentation (Q := Q) x = 1) (hspin : spinRepresentation Q x ≠ 1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End R (SpinorModule (R := R) (M := M) Q),
        spinRepresentation Q = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  intro hfactor
  rcases hfactor with ⟨ρ, hρ⟩
  have hρx :
      spinRepresentation Q x = ρ (spinIsometryRepresentation (Q := Q) x) := by
    simpa using congrArg
      (fun f : spinGroup Q →* Module.End R (SpinorModule (R := R) (M := M) Q) => f x) hρ
  apply hspin
  calc
    spinRepresentation Q x = ρ (spinIsometryRepresentation (Q := Q) x) := hρx
    _ = ρ 1 := by rw [hker]
    _ = 1 := map_one ρ

/-- A nontrivial scalar spin element gives a concrete obstruction to factoring the spin
representation through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_coe_eq_algebraMap_of_ne_one
    (x : spinGroup Q) (r : R)
    (hx : (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r) (hr : r ≠ 1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End R (SpinorModule (R := R) (M := M) Q),
        spinRepresentation Q = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  apply spinRepresentation_not_factor_through_isometry_of_kernel_witness (Q := Q) x
  · exact spinIsometryRepresentation_eq_one_of_coe_eq_algebraMap (Q := Q) x r hx
  · exact spinRepresentation_ne_one_of_coe_eq_algebraMap_of_ne_one (Q := Q) x r hx hr

/-- The Clifford unit attached to a vector with invertible quadratic norm. -/
noncomputable def cliffordIotaUnit (a : M) [Invertible (Q a)] : (CliffordAlgebra Q)ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) (isUnit_of_invertible (Q a))).unit

omit [Invertible (2 : R)] in
@[simp]
theorem coe_cliffordIotaUnit (a : M) [Invertible (Q a)] :
    ((cliffordIotaUnit (Q := Q) a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q a :=
  IsUnit.unit_spec <| CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) (isUnit_of_invertible (Q a))

/-- A vector with invertible quadratic norm determines an element of the Lipschitz group. -/
noncomputable def cliffordIotaLipschitz (a : M) [Invertible (Q a)] : lipschitzGroup Q :=
  ⟨cliffordIotaUnit (Q := Q) a, by
    unfold lipschitzGroup
    exact Subgroup.subset_closure <| by
      change (((cliffordIotaUnit (Q := Q) a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∈
        Set.range (CliffordAlgebra.ι Q)
      exact ⟨a, coe_cliffordIotaUnit (Q := Q) a⟩⟩

omit [Invertible (2 : R)] in
@[simp]
theorem coe_cliffordIotaLipschitz (a : M) [Invertible (Q a)] :
    (((cliffordIotaLipschitz (Q := Q) a : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) =
      CliffordAlgebra.ι Q a :=
  coe_cliffordIotaUnit (Q := Q) a

/-- The ambient Lipschitz action of an invertible vector is the explicit reflection formula
`b ↦ (⅟(Q a) * polar_Q(a,b)) • a - b`. -/
theorem lipschitzLinearRepresentation_apply_cliffordIota
    (a b : M) [Invertible (Q a)] :
    lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a) b =
      (⅟(Q a) * QuadraticMap.polar Q a b) • a - b := by
  let x : lipschitzGroup Q := cliffordIotaLipschitz (Q := Q) a
  letI : Invertible (CliffordAlgebra.ι Q a) := (cliffordIotaUnit (Q := Q) a).invertible
  apply cliffordIota_injective (Q := Q)
  rw [lipschitzLinearRepresentation_apply, lipschitzLinearEquiv_ι, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct]
  change (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * CliffordAlgebra.ι Q b *
      ↑((x : (CliffordAlgebra Q)ˣ)⁻¹)) =
    CliffordAlgebra.ι Q ((⅟(Q a) * QuadraticMap.polar Q a b) • a - b)
  simp [x, cliffordIotaLipschitz]
  rw [← invOf_units (cliffordIotaUnit (Q := Q) a)]
  simpa [cliffordIotaLipschitz, cliffordIotaUnit] using
    (CliffordAlgebra.ι_mul_ι_mul_invOf_ι (Q := Q) a b)

/-- The ambient Lipschitz action of an invertible vector fixes that vector. -/
theorem lipschitzLinearRepresentation_apply_cliffordIota_self
    (a : M) [Invertible (Q a)] :
    lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a) a = a := by
  rw [lipschitzLinearRepresentation_apply_cliffordIota (Q := Q) a a]
  have hcoef : (⅟(Q a) * QuadraticMap.polar Q a a : R) = 2 := by
    have hq1 : (⅟(Q a) * Q a : R) = 1 := invOf_mul_self (Q a)
    rw [QuadraticMap.polar_self, two_smul, mul_add, hq1]
    simpa using (two_mul (1 : R)).symm
  rw [hcoef]
  simp [two_smul, sub_eq_add_neg, add_assoc]

/-- The ambient Lipschitz action of an invertible vector acts by negation on vectors orthogonal to
it. -/
theorem lipschitzLinearRepresentation_apply_cliffordIota_of_isOrtho
    (a b : M) [Invertible (Q a)] (hab : Q.IsOrtho a b) :
    lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a) b = -b := by
  rw [lipschitzLinearRepresentation_apply_cliffordIota (Q := Q) a b, hab.polar_eq_zero]
  simp

/-- The ambient Lipschitz action of an invertible vector preserves its span. -/
theorem lipschitzLinearRepresentation_mem_span_singleton_cliffordIota
    (a b : M) [Invertible (Q a)] (hb : b ∈ R ∙ a) :
    lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a) b ∈ R ∙ a := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [map_smul, lipschitzLinearRepresentation_apply_cliffordIota_self (Q := Q) a]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-- The ambient Lipschitz action of an invertible vector differs from `-id` by a vector in its
span. -/
theorem lipschitzLinearRepresentation_add_self_mem_span_singleton_cliffordIota
    (a b : M) [Invertible (Q a)] :
    lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a) b + b ∈ R ∙ a := by
  rw [lipschitzLinearRepresentation_apply_cliffordIota (Q := Q) a b]
  simpa [sub_eq_add_neg, add_assoc] using
    (Submodule.smul_mem (R ∙ a) (⅟(Q a) * QuadraticMap.polar Q a b)
      (Submodule.mem_span_singleton_self a))

/-- The ambient Lipschitz action of an invertible vector preserves its span as a submodule. -/
theorem lipschitzLinearRepresentation_span_singleton_le_comap_cliffordIota
    (a : M) [Invertible (Q a)] :
    (R ∙ a) ≤ (R ∙ a).comap
      (((lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) :
          M ≃ₗ[R] M) : M →ₗ[R] M) := by
  intro b hb
  exact lipschitzLinearRepresentation_mem_span_singleton_cliffordIota (Q := Q) a b hb

/-- Modulo the line spanned by an invertible vector, its ambient Lipschitz action is `-id`. -/
theorem lipschitzLinearRepresentation_mapQ_span_singleton_eq_neg_id_cliffordIota
    (a : M) [Invertible (Q a)] :
    (R ∙ a).mapQ (R ∙ a)
      ((((lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) :
          M ≃ₗ[R] M) : M →ₗ[R] M))
      (lipschitzLinearRepresentation_span_singleton_le_comap_cliffordIota (Q := Q) a) =
      (-1 : R) • LinearMap.id := by
  ext b
  apply (Submodule.Quotient.eq (R ∙ a)).mpr
  simpa [sub_eq_add_neg, add_assoc] using
    lipschitzLinearRepresentation_add_self_mem_span_singleton_cliffordIota (Q := Q) a b

/-- On the line spanned by an invertible vector, its ambient Lipschitz action is the identity. -/
theorem lipschitzLinearRepresentation_restrict_span_singleton_eq_id_cliffordIota
    (a : M) [Invertible (Q a)] :
    ((((lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) :
        M ≃ₗ[R] M) : M →ₗ[R] M).restrict
      (lipschitzLinearRepresentation_span_singleton_le_comap_cliffordIota (Q := Q) a)) =
      LinearMap.id := by
  ext b
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp b.2
  have hc_mem : c • a ∈ R ∙ a := Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)
  have hb : b = ⟨c • a, hc_mem⟩ := by
    apply Subtype.ext
    simpa using hc.symm
  rw [hb]
  simpa [LinearMap.restrict_apply, map_smul, lipschitzLinearRepresentation_apply,
    lipschitzLinearEquiv_apply] using
    congrArg (fun m => c • m)
      (lipschitzLinearRepresentation_apply_cliffordIota_self (Q := Q) a)

omit [Invertible (2 : R)] in
/-- A vector of quadratic norm `-1` defines a pin element. -/
theorem iota_mem_pinGroup_of_quadratic_eq_neg_one (m : M) (hq : Q m = -1) :
    CliffordAlgebra.ι Q m ∈ pinGroup Q := by
  let u : (CliffordAlgebra Q)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) (by rw [hq]; exact isUnit_neg_one)).unit
  have hu : (u : CliffordAlgebra Q) = CliffordAlgebra.ι Q m := by
    exact IsUnit.unit_spec <|
      CliffordAlgebra.isUnit_ι_of_isUnit (Q := Q) (by rw [hq]; exact isUnit_neg_one)
  have huPin : (u : CliffordAlgebra Q) ∈ pinGroup Q := by
    rw [pinGroup.units_mem_iff]
    constructor
    · unfold lipschitzGroup
      exact Subgroup.subset_closure <| by
        change (u : CliffordAlgebra Q) ∈ Set.range (CliffordAlgebra.ι Q)
        exact ⟨m, hu⟩
    · refine (Unitary.mem_iff).2 ?_
      constructor
      · calc
          star (u : CliffordAlgebra Q) * (u : CliffordAlgebra Q) =
              star (CliffordAlgebra.ι Q m) * CliffordAlgebra.ι Q m := by
                rw [hu]
          _ = (-CliffordAlgebra.ι Q m) * CliffordAlgebra.ι Q m := by
                rw [CliffordAlgebra.star_ι]
          _ = -(CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m) := by
                rw [neg_mul]
          _ = -algebraMap R (CliffordAlgebra Q) (Q m) := by
                rw [CliffordAlgebra.ι_sq_scalar]
          _ = 1 := by
                rw [hq]
                simp
      · calc
          (u : CliffordAlgebra Q) * star (u : CliffordAlgebra Q) =
              CliffordAlgebra.ι Q m * star (CliffordAlgebra.ι Q m) := by
                rw [hu]
          _ = CliffordAlgebra.ι Q m * (-CliffordAlgebra.ι Q m) := by
                rw [CliffordAlgebra.star_ι]
          _ = -(CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m) := by
                rw [mul_neg]
          _ = -algebraMap R (CliffordAlgebra Q) (Q m) := by
                rw [CliffordAlgebra.ι_sq_scalar]
          _ = 1 := by
                rw [hq]
                simp
  rw [← hu]
  exact huPin

omit [Invertible (2 : R)] in
/-- The canonical pin element attached to a vector of quadratic norm `-1`. -/
noncomputable def pinIotaOfQuadraticEqNegOne (m : M) (hq : Q m = -1) : pinGroup Q :=
  ⟨CliffordAlgebra.ι Q m, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) m hq⟩

omit [Invertible (2 : R)] in
@[simp] theorem coe_pinIotaOfQuadraticEqNegOne (m : M) (hq : Q m = -1) :
    ((pinIotaOfQuadraticEqNegOne (Q := Q) m hq : pinGroup Q) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q m :=
  rfl

omit [Invertible (2 : R)] in
/-- The canonical spin element attached to a pair of vectors of quadratic norm `-1`. -/
noncomputable def spinIotaPairOfQuadraticEqNegOne (a b : M) (ha : Q a = -1) (hb : Q b = -1) :
    spinGroup Q := by
  refine ⟨CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b, ?_⟩
  rw [spinGroup.mem_iff]
  constructor
  · exact (pinGroup Q).mul_mem
      (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a ha)
      (iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) b hb)
  · simpa [CliffordAlgebra.even] using CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := Q) a b

omit [Invertible (2 : R)] in
@[simp] theorem coe_spinIotaPairOfQuadraticEqNegOne (a b : M) (ha : Q a = -1) (hb : Q b = -1) :
    ((spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb : spinGroup Q) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b :=
  rfl

/-- The ambient pin action of a norm-`-1` vector is the explicit conjugation formula
`b ↦ (⅟(Q a) * polar_Q(a,b)) • a - b`, specialized to `Q a = -1`. -/
theorem pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one
    (a b : M) (hq : Q a = -1) :
    pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩ b =
      (-(QuadraticMap.polar Q a b)) • a - b := by
  let x : pinGroup Q :=
    ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩
  letI : Invertible (Q a) := by
    rw [hq]
    exact isUnit_neg_one.invertible
  letI : Invertible (CliffordAlgebra.ι Q a) := CliffordAlgebra.invertibleιOfInvertible (Q := Q) a
  have hInv : (⅟(Q a) : R) = -1 := by
    apply invOf_eq_right_inv
    rw [hq]
    simp
  apply cliffordIota_injective (Q := Q)
  rw [pinLinearRepresentation_apply, pinLinearEquiv_ι, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct]
  rw [← invOf_units (pinGroup.toUnits x)]
  simp [x]
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  rw [hInv]
  simp

/-- The ambient pin action of a norm-`-1` vector fixes that vector. -/
theorem pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one_self
    (a : M) (hq : Q a = -1) :
    pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩ a = a := by
  rw [pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one (Q := Q) a a hq]
  rw [QuadraticMap.polar_self, hq]
  have htwo : -(2 • (-1 : R)) = (2 : R) := by norm_num
  rw [htwo]
  simp [two_smul, sub_eq_add_neg, add_assoc]

/-- The ambient pin action of a norm-`-1` vector acts by negation on vectors orthogonal to it. -/
theorem pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one_of_isOrtho
    (a b : M) (hq : Q a = -1) (hab : Q.IsOrtho a b) :
    pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩ b = -b := by
  rw [pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one (Q := Q) a b hq, hab.polar_eq_zero]
  simp

/-- The ambient pin action of a norm-`-1` vector preserves its span. -/
theorem pinLinearRepresentation_mem_span_singleton_of_quadratic_eq_neg_one
    (a b : M) (hq : Q a = -1) (hb : b ∈ R ∙ a) :
    pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩ b ∈ R ∙ a := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [map_smul, pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one_self (Q := Q) a hq]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-- The ambient pin action of a norm-`-1` vector differs from `-id` by a vector in its span. -/
theorem pinLinearRepresentation_add_self_mem_span_singleton_of_quadratic_eq_neg_one
    (a b : M) (hq : Q a = -1) :
    pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩ b + b ∈
      R ∙ a := by
  rw [pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one (Q := Q) a b hq]
  simpa [sub_eq_add_neg, add_assoc] using
    (Submodule.smul_mem (R ∙ a) (-(QuadraticMap.polar Q a b))
      (Submodule.mem_span_singleton_self a))

/-- The ambient pin action of a norm-`-1` vector preserves its span as a submodule. -/
theorem pinLinearRepresentation_span_singleton_le_comap_of_quadratic_eq_neg_one
    (a : M) (hq : Q a = -1) :
    (R ∙ a) ≤ (R ∙ a).comap
      (((pinLinearRepresentation (Q := Q)
          ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩) :
            M ≃ₗ[R] M) : M →ₗ[R] M) := by
  intro b hb
  exact pinLinearRepresentation_mem_span_singleton_of_quadratic_eq_neg_one (Q := Q) a b hq hb

/-- Modulo the line spanned by a norm-`-1` vector, its ambient pin action is `-id`. -/
theorem pinLinearRepresentation_mapQ_span_singleton_eq_neg_id_of_quadratic_eq_neg_one
    (a : M) (hq : Q a = -1) :
    (R ∙ a).mapQ (R ∙ a)
      ((((pinLinearRepresentation (Q := Q)
          ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩) :
            M ≃ₗ[R] M) : M →ₗ[R] M))
      (pinLinearRepresentation_span_singleton_le_comap_of_quadratic_eq_neg_one (Q := Q) a hq) =
      (-1 : R) • LinearMap.id := by
  ext b
  apply (Submodule.Quotient.eq (R ∙ a)).mpr
  simpa [sub_eq_add_neg, add_assoc] using
    pinLinearRepresentation_add_self_mem_span_singleton_of_quadratic_eq_neg_one (Q := Q) a b hq

/-- On the line spanned by a norm-`-1` vector, its ambient pin action is the identity. -/
theorem pinLinearRepresentation_restrict_span_singleton_eq_id_of_quadratic_eq_neg_one
    (a : M) (hq : Q a = -1) :
    ((((pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩) :
          M ≃ₗ[R] M) : M →ₗ[R] M).restrict
      (pinLinearRepresentation_span_singleton_le_comap_of_quadratic_eq_neg_one (Q := Q) a hq)) =
      LinearMap.id := by
  ext b
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp b.2
  have hc_mem : c • a ∈ R ∙ a := Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)
  have hb : b = ⟨c • a, hc_mem⟩ := by
    apply Subtype.ext
    simpa using hc.symm
  rw [hb]
  simpa [LinearMap.restrict_apply, map_smul, pinLinearRepresentation_apply, pinLinearEquiv_apply] using
    congrArg (fun m => c • m)
      (pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one_self (Q := Q) a hq)

section Field

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) [Invertible (2 : K)] [FiniteDimensional K V]

/-- Over a finite-dimensional vector space, the ambient pin action of a norm-`-1` generator has
determinant `(-1)^(dim(V / Ka))`, where `Ka` is the span of that vector. -/
theorem pinLinearRepresentation_det_of_quadratic_eq_neg_one
    (a : V) (hq : Q a = -1) :
    LinearMap.det
        ((((pinLinearRepresentation (Q := Q)
            ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩) :
              V ≃ₗ[K] V) : V →ₗ[K] V)) =
      (-1 : K) ^ Module.finrank K (V ⧸ (K ∙ a)) := by
  let f : V →ₗ[K] V :=
    (((pinLinearRepresentation (Q := Q)
        ⟨CliffordAlgebra.ι Q a, iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) a hq⟩) :
          V ≃ₗ[K] V) : V →ₗ[K] V)
  let p : Submodule K V := K ∙ a
  change LinearMap.det f = (-1 : K) ^ Module.finrank K (V ⧸ p)
  have hp : p ≤ p.comap f := by
    simpa [p, f] using
      pinLinearRepresentation_span_singleton_le_comap_of_quadratic_eq_neg_one (Q := Q) a hq
  have hrestrict : f.restrict hp = LinearMap.id := by
    simpa [p, f] using
      pinLinearRepresentation_restrict_span_singleton_eq_id_of_quadratic_eq_neg_one (Q := Q) a hq
  have hmapQ : p.mapQ p f hp = (-1 : K) • LinearMap.id := by
    simpa [p, f] using
      pinLinearRepresentation_mapQ_span_singleton_eq_neg_id_of_quadratic_eq_neg_one (Q := Q) a hq
  calc
    LinearMap.det f = LinearMap.det (f.restrict hp) * LinearMap.det (p.mapQ p f hp) := by
      simpa [p, f] using LinearMap.det_eq_det_mul_det (W := p) f hp
    _ = 1 * LinearMap.det ((-1 : K) • (LinearMap.id : (V ⧸ p) →ₗ[K] (V ⧸ p))) := by
      simp [hrestrict, hmapQ]
    _ = (-1 : K) ^ Module.finrank K (V ⧸ p) := by
      rw [LinearMap.det_smul, LinearMap.det_id]
      simp

/-- Over a finite-dimensional vector space, the ambient Lipschitz action of an invertible vector
has determinant `(-1)^(dim V - 1)`. -/
theorem lipschitzLinearRepresentation_det_toLinearMap_cliffordIota
    (a : V) [Invertible (Q a)] :
    LinearMap.det
        ((((lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) :
            V ≃ₗ[K] V) : V →ₗ[K] V)) =
      (-1 : K) ^ (Module.finrank K V - 1) := by
  let f : V →ₗ[K] V :=
    (((lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) :
        V ≃ₗ[K] V) : V →ₗ[K] V)
  let p : Submodule K V := K ∙ a
  change LinearMap.det f = (-1 : K) ^ (Module.finrank K V - 1)
  have hp : p ≤ p.comap f := by
    simpa [p, f] using
      lipschitzLinearRepresentation_span_singleton_le_comap_cliffordIota (Q := Q) a
  have hrestrict : f.restrict hp = LinearMap.id := by
    simpa [p, f] using
      lipschitzLinearRepresentation_restrict_span_singleton_eq_id_cliffordIota (Q := Q) a
  have hmapQ : p.mapQ p f hp = (-1 : K) • LinearMap.id := by
    simpa [p, f] using
      lipschitzLinearRepresentation_mapQ_span_singleton_eq_neg_id_cliffordIota (Q := Q) a
  have ha : a ≠ 0 := by
    intro ha
    exact (isUnit_of_invertible (Q a)).ne_zero (by simp [ha])
  have hfin : Module.finrank K (V ⧸ p) = Module.finrank K V - 1 := by
    have hdim : Module.finrank K (V ⧸ p) + 1 = Module.finrank K V := by
      simpa [p, finrank_span_singleton ha] using p.finrank_quotient_add_finrank
    exact Nat.eq_sub_of_add_eq hdim
  calc
    LinearMap.det f = LinearMap.det (f.restrict hp) * LinearMap.det (p.mapQ p f hp) := by
      simpa [p, f] using LinearMap.det_eq_det_mul_det (W := p) f hp
    _ = 1 * LinearMap.det ((-1 : K) • (LinearMap.id : (V ⧸ p) →ₗ[K] (V ⧸ p))) := by
      simp [hrestrict, hmapQ]
    _ = (-1 : K) ^ Module.finrank K (V ⧸ p) := by
      rw [LinearMap.det_smul, LinearMap.det_id]
      simp
    _ = (-1 : K) ^ (Module.finrank K V - 1) := by rw [hfin]

/-- Unit-valued determinant version of
`lipschitzLinearRepresentation_det_toLinearMap_cliffordIota`. -/
theorem lipschitzLinearRepresentation_det_cliffordIota
    (a : V) [Invertible (Q a)] :
    LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)) =
      (-1 : Kˣ) ^ (Module.finrank K V - 1) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  simpa using lipschitzLinearRepresentation_det_toLinearMap_cliffordIota (Q := Q) a

private def lipschitzVal (x : lipschitzGroup Q) : CliffordAlgebra Q :=
  ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)

/-- `lipschitzLinearRepresentationDetParity x` records the two determinant/involution patterns
compatible with multiplicative generation by vectors. -/
def lipschitzLinearRepresentationDetParity (x : lipschitzGroup Q) : Prop :=
  (CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) = lipschitzVal (Q := Q) x ∧
      LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) = 1)
    ∨
  (CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) = -(lipschitzVal (Q := Q) x) ∧
      LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) =
        (-1 : Kˣ) ^ (Module.finrank K V - 1))

theorem lipschitzLinearRepresentationDetParity_cliffordIota
    (a : V) [Invertible (Q a)] :
    lipschitzLinearRepresentationDetParity (Q := Q) (cliffordIotaLipschitz (Q := Q) a) := by
  right
  constructor
  · change CliffordAlgebra.involute (Q := Q) (CliffordAlgebra.ι Q a) = -CliffordAlgebra.ι Q a
    simp
  · exact lipschitzLinearRepresentation_det_cliffordIota (Q := Q) a

omit [Invertible (2 : K)] [FiniteDimensional K V] in
@[simp]
theorem coe_cliffordIotaLipschitz_inv (a : V) [Invertible (Q a)] :
    lipschitzVal (Q := Q) ((cliffordIotaLipschitz (Q := Q) a)⁻¹) =
      (⅟(Q a)) • CliffordAlgebra.ι Q a := by
  letI : Invertible (CliffordAlgebra.ι Q a) := (cliffordIotaUnit (Q := Q) a).invertible
  change (⅟(CliffordAlgebra.ι Q a) : CliffordAlgebra Q) = _
  simpa using (CliffordAlgebra.invOf_ι (Q := Q) a)

theorem lipschitzLinearRepresentationDetParity_inv_cliffordIota
    (a : V) [Invertible (Q a)] :
    lipschitzLinearRepresentationDetParity (Q := Q) ((cliffordIotaLipschitz (Q := Q) a)⁻¹) := by
  right
  constructor
  · rw [coe_cliffordIotaLipschitz_inv (Q := Q) a]
    simp [CliffordAlgebra.involute_ι, map_smul]
  · have hdetInv :
        LinearEquiv.det
            (lipschitzLinearRepresentation (Q := Q) ((cliffordIotaLipschitz (Q := Q) a)⁻¹)) =
          (LinearEquiv.det
            (lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a)))⁻¹ := by
      rw [(lipschitzLinearRepresentation (Q := Q)).map_inv]
      exact map_inv (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ)
        (lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a))
    rw [hdetInv, lipschitzLinearRepresentation_det_cliffordIota (Q := Q) a]
    let n : ℕ := Module.finrank K V - 1
    have hsq : ((-1 : Kˣ) ^ n) * ((-1 : Kˣ) ^ n) = 1 := by
      apply Units.ext
      change (((-1 : K) ^ n) * ((-1 : K) ^ n)) = 1
      rw [← pow_add, ← two_mul n, pow_mul]
      simp
    exact inv_eq_of_mul_eq_one_left hsq

omit [FiniteDimensional K V] in
theorem lipschitzLinearRepresentationDetParity_mul {x y : lipschitzGroup Q}
    (hx : lipschitzLinearRepresentationDetParity (Q := Q) x)
    (hy : lipschitzLinearRepresentationDetParity (Q := Q) y) :
    lipschitzLinearRepresentationDetParity (Q := Q) (x * y) := by
  have hinvoluteMul :
      CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) (x * y)) =
        CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) *
          CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) y) := by
    change CliffordAlgebra.involute (Q := Q)
        (lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y) = _
    exact map_mul (CliffordAlgebra.involute (Q := Q))
      (lipschitzVal (Q := Q) x) (lipschitzVal (Q := Q) y)
  have hdetMul :
      LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) (x * y)) =
        LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) *
          LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) y) := by
    rw [(lipschitzLinearRepresentation (Q := Q)).map_mul]
    exact map_mul (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ)
      (lipschitzLinearRepresentation (Q := Q) x) (lipschitzLinearRepresentation (Q := Q) y)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left
    constructor
    · calc
        CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) (x * y)) =
            CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) *
              CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) y) := hinvoluteMul
        _ = lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y := by rw [hx.1, hy.1]
        _ = lipschitzVal (Q := Q) (x * y) := by rfl
    · rw [hdetMul, hx.2, hy.2]
      simp
  · right
    constructor
    · calc
        CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) (x * y)) =
            CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) *
              CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) y) := hinvoluteMul
        _ = lipschitzVal (Q := Q) x * (-(lipschitzVal (Q := Q) y)) := by rw [hx.1, hy.1]
        _ = -(lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y) := by rw [mul_neg]
        _ = -(lipschitzVal (Q := Q) (x * y)) := by rfl
    · rw [hdetMul, hx.2, hy.2]
      simp
  · right
    constructor
    · calc
        CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) (x * y)) =
            CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) *
              CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) y) := hinvoluteMul
        _ = (-(lipschitzVal (Q := Q) x)) * lipschitzVal (Q := Q) y := by rw [hx.1, hy.1]
        _ = -(lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y) := by rw [neg_mul]
        _ = -(lipschitzVal (Q := Q) (x * y)) := by rfl
    · rw [hdetMul, hx.2, hy.2]
      simp
  · left
    constructor
    · calc
        CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) (x * y)) =
            CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) x) *
              CliffordAlgebra.involute (Q := Q) (lipschitzVal (Q := Q) y) := hinvoluteMul
        _ = (-(lipschitzVal (Q := Q) x)) * (-(lipschitzVal (Q := Q) y)) := by rw [hx.1, hy.1]
        _ = lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y := by simp
        _ = lipschitzVal (Q := Q) (x * y) := by rfl
    · rw [hdetMul, hx.2, hy.2]
      let n : ℕ := Module.finrank K V - 1
      have hsq : ((-1 : Kˣ) ^ n) * ((-1 : Kˣ) ^ n) = 1 := by
        apply Units.ext
        change (((-1 : K) ^ n) * ((-1 : K) ^ n)) = 1
        rw [← pow_add, ← two_mul n, pow_mul]
        simp
      have hd : (((-1 : Kˣ) ^ n)⁻¹) = (-1 : Kˣ) ^ n :=
        inv_eq_of_mul_eq_one_left hsq
      calc
        (-1 : Kˣ) ^ n * (-1 : Kˣ) ^ n = ((-1 : Kˣ) ^ n)⁻¹ * ((-1 : Kˣ) ^ n) := by rw [hd]
        _ = 1 := by simp

/-- Every Lipschitz element acts with determinant either `1` or the determinant of an invertible
vector generator, according to its Clifford parity. -/
theorem lipschitzLinearRepresentation_detParity (x : lipschitzGroup Q) :
    lipschitzLinearRepresentationDetParity (Q := Q) x := by
  let s : Set (CliffordAlgebra Q)ˣ := ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q))
  let p : (g : (CliffordAlgebra Q)ˣ) → g ∈ Subgroup.closure s → Prop :=
    fun g hg =>
      lipschitzLinearRepresentationDetParity (Q := Q)
        ⟨g, by simpa [lipschitzGroup, s] using hg⟩
  have hx : ((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) ∈ Subgroup.closure s := by
    have hx0 := x.property
    simp [lipschitzGroup, s] at hx0 ⊢
  exact Subgroup.closure_induction'' (s := s) (p := p)
    (fun g hg => by
      obtain ⟨a, ha⟩ := hg
      letI := g.invertible
      letI : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
      letI : Invertible (Q a) := CliffordAlgebra.invertibleOfInvertibleι (Q := Q) a
      have hg' : g = cliffordIotaUnit (Q := Q) a := by
        apply Units.ext
        simpa [cliffordIotaUnit] using ha.symm
      simpa [p, hg'] using
        lipschitzLinearRepresentationDetParity_cliffordIota (Q := Q) a)
    (fun g hg => by
      obtain ⟨a, ha⟩ := hg
      letI := g.invertible
      letI : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
      letI : Invertible (Q a) := CliffordAlgebra.invertibleOfInvertibleι (Q := Q) a
      have hg' : g = cliffordIotaUnit (Q := Q) a := by
        apply Units.ext
        simpa [cliffordIotaUnit] using ha.symm
      simpa [p, hg'] using
        lipschitzLinearRepresentationDetParity_inv_cliffordIota (Q := Q) a)
    (by
      left
      constructor
      · simp [lipschitzVal]
      · change LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) (1 : lipschitzGroup Q)) = 1
        rw [(lipschitzLinearRepresentation (Q := Q)).map_one]
        simp)
    (fun g h hg hh hg' hh' => by
      simpa [p] using lipschitzLinearRepresentationDetParity_mul (Q := Q) hg' hh')
    hx

/-- The ambient spin representation always has determinant `1`. -/
theorem spinLinearRepresentation_det_eq_one (x : spinGroup Q) :
    LinearEquiv.det (spinLinearRepresentation (Q := Q) x) = 1 := by
  let xL : lipschitzGroup Q :=
    ⟨spinGroup.toUnits x, spinGroup.units_mem_lipschitzGroup x.prop⟩
  rcases lipschitzLinearRepresentation_detParity (Q := Q) xL with h | h
  · simpa [xL, lipschitzLinearRepresentation_toUnits_spinGroup (Q := Q) x] using h.2
  · have hx_even : CliffordAlgebra.involute (Q := Q) (x : CliffordAlgebra Q) = x :=
      spinGroup.involute_eq x.prop
    have hx_odd : CliffordAlgebra.involute (Q := Q) (x : CliffordAlgebra Q) = -(x : CliffordAlgebra Q) := by
      simpa [xL] using h.1
    have hneg : (x : CliffordAlgebra Q) = -(x : CliffordAlgebra Q) := by
      calc
        (x : CliffordAlgebra Q) = CliffordAlgebra.involute (Q := Q) (x : CliffordAlgebra Q) := by
          simpa using hx_even.symm
        _ = -(x : CliffordAlgebra Q) := hx_odd
    have htwo : (2 : K) • (x : CliffordAlgebra Q) = 0 := by
      calc
        (2 : K) • (x : CliffordAlgebra Q) = (x : CliffordAlgebra Q) + x := by simp [two_smul]
        _ = (x : CliffordAlgebra Q) + (-(x : CliffordAlgebra Q)) := by
              exact congrArg (fun t : CliffordAlgebra Q => (x : CliffordAlgebra Q) + t) hneg
        _ = 0 := by simp
    have htwo_ne_zero : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
    have hx_zero : (x : CliffordAlgebra Q) = 0 := by
      exact (smul_eq_zero.mp htwo).resolve_left htwo_ne_zero
    exact False.elim ((Units.ne_zero (spinGroup.toUnits x)) (by simpa using hx_zero))

/-- The ambient spin action factors through the special orthogonal group over finite-dimensional
fields. -/
noncomputable def spinSpecialOrthogonalRepresentationFiniteDimensional :
    spinGroup Q →* Q.specialOrthogonalGroup :=
  spinSpecialOrthogonalRepresentation (Q := Q) (spinLinearRepresentation_det_eq_one (Q := Q))

@[simp]
theorem coe_spinSpecialOrthogonalRepresentationFiniteDimensional (x : spinGroup Q) :
    ↑(spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q) x) =
      spinIsometryRepresentation (Q := Q) x := rfl

@[simp]
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_comp_subtype :
    (Q.specialOrthogonalGroup.subtype).comp
        (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)) =
      spinIsometryRepresentation (Q := Q) := by
  ext x
  rfl

omit [Invertible (2 : K)] [FiniteDimensional K V] in
@[simp]
theorem spinGroupToPinGroup_spinIotaPairOfQuadraticEqNegOne
    (a b : V) (ha : Q a = -1) (hb : Q b = -1) :
    spinGroupToPinGroup (Q := Q) (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb) =
      pinIotaOfQuadraticEqNegOne (Q := Q) a ha * pinIotaOfQuadraticEqNegOne (Q := Q) b hb := by
  apply Subtype.ext
  rfl

omit [FiniteDimensional K V] in
theorem spinIsometryRepresentation_spinIotaPairOfQuadraticEqNegOne
    (a b : V) (ha : Q a = -1) (hb : Q b = -1) :
    spinIsometryRepresentation (Q := Q) (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb) =
      pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
        pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) b hb) := by
  calc
    spinIsometryRepresentation (Q := Q) (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb) =
        pinIsometryRepresentation (Q := Q)
          ((pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
            (pinIotaOfQuadraticEqNegOne (Q := Q) b hb)) := by
          ext m
          have hlin :
              pinLinearRepresentation (Q := Q)
                  ((pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
                    (pinIotaOfQuadraticEqNegOne (Q := Q) b hb)) =
                spinLinearRepresentation (Q := Q)
                  (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb) := by
            calc
              pinLinearRepresentation (Q := Q)
                  ((pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
                    (pinIotaOfQuadraticEqNegOne (Q := Q) b hb)) =
                  pinLinearRepresentation (Q := Q)
                    (spinGroupToPinGroup (Q := Q)
                      (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb)) := by
                        rw [spinGroupToPinGroup_spinIotaPairOfQuadraticEqNegOne (Q := Q)]
              _ = spinLinearRepresentation (Q := Q)
                    (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb) := by
                      simpa using pinLinearRepresentation_spinGroupToPinGroup (Q := Q)
                        (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb)
          exact congrArg (fun e : V ≃ₗ[K] V => e m) hlin.symm
    _ = pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
          pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) b hb) := by
          rw [(pinIsometryRepresentation (Q := Q)).map_mul]

/-- A packaged pair-reflection lift in the special orthogonal target. Proving these generators span
`SO(V,Q)` is the remaining surjectivity gap for the ambient covering map. -/
noncomputable def spinSpecialOrthogonalPairGenerator
    (a b : V) (ha : Q a = -1) (hb : Q b = -1) : Q.specialOrthogonalGroup :=
  spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)
    (spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb)

@[simp]
theorem coe_spinSpecialOrthogonalPairGenerator
    (a b : V) (ha : Q a = -1) (hb : Q b = -1) :
    ↑(spinSpecialOrthogonalPairGenerator (Q := Q) a b ha hb) =
      pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) a ha) *
        pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) b hb) := by
  simpa [spinSpecialOrthogonalPairGenerator] using
    spinIsometryRepresentation_spinIotaPairOfQuadraticEqNegOne (Q := Q) a b ha hb

/-- The set of canonical two-reflection lifts whose generation would imply surjectivity of the
ambient spin covering map. -/
def spinSpecialOrthogonalPairGeneratorSet : Set (Q.specialOrthogonalGroup) :=
  Set.range fun p : {ab : V × V // Q ab.1 = -1 ∧ Q ab.2 = -1} =>
    spinSpecialOrthogonalPairGenerator (Q := Q) p.1.1 p.1.2 p.2.1 p.2.2

theorem spinSpecialOrthogonalPairGeneratorSet_subset_range :
    spinSpecialOrthogonalPairGeneratorSet (Q := Q) ⊆
      MonoidHom.range (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨_, rfl⟩

/-- Surjectivity of the ambient spin covering map reduces to showing that the canonical
two-reflection lifts generate `SO(V,Q)`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top
    (hgen : Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := Q)) = ⊤) :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)) := by
  have hrange :
      MonoidHom.range (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (Subgroup.closure_le (K := MonoidHom.range
      (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)))).2
      (spinSpecialOrthogonalPairGeneratorSet_subset_range (Q := Q))
  exact MonoidHom.range_eq_top.mp hrange

end Field

omit [Invertible (2 : R)] in
/-- If the quadratic form represents `-1`, then the scalar `-1` lies in the spin group. -/
theorem neg_one_mem_spinGroup_of_quadratic_eq_neg_one (m : M) (hq : Q m = -1) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  rw [spinGroup.mem_iff]
  constructor
  · have hm : CliffordAlgebra.ι Q m ∈ pinGroup Q :=
      iota_mem_pinGroup_of_quadratic_eq_neg_one (Q := Q) m hq
    have hmul : CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m ∈ pinGroup Q :=
      (pinGroup Q).mul_mem hm hm
    simpa using (show algebraMap R (CliffordAlgebra Q) (-1) ∈ pinGroup Q by
      rw [← hq, ← CliffordAlgebra.ι_sq_scalar]
      exact hmul)
  · convert (CliffordAlgebra.even Q).algebraMap_mem (-1 : R) using 1
    · simp

/-- If the quadratic form represents `-1` and `-1 ≠ 1`, the spin representation cannot factor
through the ambient isometry representation. -/
theorem spinRepresentation_not_factor_through_isometry_of_exists_quadratic_eq_neg_one
    (hQ : ∃ m, Q m = -1) (hneq : (-1 : R) ≠ 1) :
    ¬ ∃ ρ : Q.IsometryEquiv Q →* Module.End R (SpinorModule (R := R) (M := M) Q),
        spinRepresentation Q = ρ.comp (spinIsometryRepresentation (Q := Q)) := by
  rcases hQ with ⟨m, hm⟩
  let x : spinGroup Q := ⟨-1, neg_one_mem_spinGroup_of_quadratic_eq_neg_one (Q := Q) m hm⟩
  apply spinRepresentation_not_factor_through_isometry_of_coe_eq_algebraMap_of_ne_one
    (Q := Q) x (-1)
  · change (-1 : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) (-1)
    simp
  · exact hneq

end Spinor
