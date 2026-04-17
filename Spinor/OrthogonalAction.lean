/-
  Ambient spin-group action on the underlying quadratic module.
-/

import Spinor.SpinRep
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Transvection.Basic

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

section DualProd

variable {K : Type*} [CommRing K]
variable {W : Type*} [AddCommGroup W] [Module K W]
variable [Invertible (2 : K)]

/-- On the split hyperbolic form `W* × W`, the reflection attached to a norm-`-1` vector
`(-f, w)` with `f(w) = 1` has an explicit coordinate formula. -/
theorem pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one
    (f : Module.Dual K W) (w : W) (hf : f w = 1)
    (d : Module.Dual K W) (u : W) :
    pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W) (-f, w)
          (by simp [QuadraticForm.dualProd, hf]))
        (d, u) =
      (((d w - f u) : K) • f - d, -((d w - f u) : K) • w - u) := by
  have hraw :
      pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
          (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W) (-f, w)
            (by simp [QuadraticForm.dualProd, hf]))
          (d, u) =
        (-d + -((f w + (f u + (-f w + -d w))) • f),
          -u + (f w + (f u + (-f w + -d w))) • w) := by
    simpa [pinIotaOfQuadraticEqNegOne, QuadraticMap.polar, QuadraticForm.dualProd,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      pinLinearRepresentation_apply_iota_of_quadratic_eq_neg_one
      (Q := QuadraticForm.dualProd K W) (-f, w) (d, u)
      (by simp [QuadraticForm.dualProd, hf])
  have hcoef : f w + (f u + (-f w + -d w)) = f u - d w := by
    ring
  have hcoef' : -((f u - d w) : K) = d w - f u := by
    ring
  have hcoef'' : f u - d w = -((d w - f u) : K) := by
    ring
  calc
    pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W) (-f, w)
          (by simp [QuadraticForm.dualProd, hf]))
        (d, u) =
      (-d + -((f w + (f u + (-f w + -d w))) • f),
        -u + (f w + (f u + (-f w + -d w))) • w) := hraw
    _ = (-d + -((f u - d w) • f), -u + (f u - d w) • w) := by
      simp [hcoef]
    _ = (-d + ((d w - f u) : K) • f, -u + (f u - d w) • w) := by
      have hneg : -((f u - d w) • f) = ((d w - f u) : K) • f := by
        rw [show -((f u - d w) • f) = (-(f u - d w) : K) • f by
          simpa using (neg_smul (f u - d w) f).symm]
        rw [hcoef']
      simp [hneg]
    _ = (((d w - f u) : K) • f - d, -((d w - f u) : K) • w - u) := by
      simp [hcoef'', sub_eq_add_neg, add_comm]

/-- The split reflection attached to `(-f, w)` swaps the primal vector `(0, w)` with the dual
vector `(-f, 0)`. -/
theorem pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one_primal
    (f : Module.Dual K W) (w : W) (hf : f w = 1) :
    pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W) (-f, w)
          (by simp [QuadraticForm.dualProd, hf]))
        (0, w) =
      (-f, 0) := by
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one (f := f) (w := w) hf
    (d := 0) (u := w)]
  ext <;> simp [hf]

/-- The split reflection attached to `(-f, w)` also swaps the dual vector `(-f, 0)` back to the
primal vector `(0, w)`. -/
theorem pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one_dual
    (f : Module.Dual K W) (w : W) (hf : f w = 1) :
    pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W) (-f, w)
          (by simp [QuadraticForm.dualProd, hf]))
        (-f, 0) =
      (0, w) := by
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one (f := f) (w := w) hf
    (d := -f) (u := 0)]
  ext <;> simp [hf]

end DualProd

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

section DualProd

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [Invertible (2 : K)] in
/-- Any linear automorphism of `W` induces a determinant-one isometry of the split hyperbolic form
`W* × W`. -/
theorem dualProdIsometry_det_eq_one (e : W ≃ₗ[K] W) :
    LinearEquiv.det
        ((QuadraticForm.dualProdIsometry (R := K) e).toLinearEquiv) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, QuadraticForm.dualProdIsometry]
  rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
  calc
    LinearMap.det ((e.dualMap.symm : Module.Dual K W →ₗ[K] Module.Dual K W)) *
        LinearMap.det (e : W →ₗ[K] W) =
      LinearMap.det ((e.dualMap.symm : Module.Dual K W →ₗ[K] Module.Dual K W)) *
        LinearMap.det (e.dualMap : Module.Dual K W →ₗ[K] Module.Dual K W) := by
          have hdet : LinearMap.det (e : W →ₗ[K] W) =
              LinearMap.det (e.dualMap : Module.Dual K W →ₗ[K] Module.Dual K W) := by
            simpa [LinearEquiv.dualMap] using (LinearMap.det_dualMap (e : W →ₗ[K] W)).symm
          rw [hdet]
    _ = 1 := LinearEquiv.det_symm_mul_det (e.dualMap)

omit [Invertible (2 : K)] in
/-- The split hyperbolic transport of a linear automorphism lies in the packaged special orthogonal
group. -/
theorem dualProdIsometry_mem_specialOrthogonalGroup (e : W ≃ₗ[K] W) :
    QuadraticForm.dualProdIsometry (R := K) e ∈
      (QuadraticForm.dualProd K W).specialOrthogonalGroup := by
  rw [QuadraticForm.mem_specialOrthogonalGroup_iff]
  exact dualProdIsometry_det_eq_one (K := K) e

omit [Invertible (2 : K)] in
/-- A linear automorphism of `W` gives a canonical element of the split special orthogonal group on
`W* × W`. -/
noncomputable def dualProdSpecialOrthogonalOfLinearEquiv (e : W ≃ₗ[K] W) :
    (QuadraticForm.dualProd K W).specialOrthogonalGroup :=
  ⟨QuadraticForm.dualProdIsometry (R := K) e,
    dualProdIsometry_mem_specialOrthogonalGroup (K := K) e⟩

omit [Invertible (2 : K)] in
@[simp]
theorem coe_dualProdSpecialOrthogonalOfLinearEquiv (e : W ≃ₗ[K] W) :
    ↑(dualProdSpecialOrthogonalOfLinearEquiv (K := K) e) =
      QuadraticForm.dualProdIsometry (R := K) e := rfl

omit [Invertible (2 : K)] in
/-- The split special-orthogonal transport of a primal transvection has the expected block
coordinate formula on `W* × W`. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_apply_transvection
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (d : Module.Dual K W) (u : W) :
    let e : W ≃ₗ[K] W := LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)
    (dualProdSpecialOrthogonalOfLinearEquiv (K := K) e).1 (d, u) =
      (d + (d w : K) • δ, u - (δ u : K) • w) := by
  let e : W ≃ₗ[K] W := LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)
  apply Prod.ext
  · ext x
    change d (e.symm x) = (d + (d w : K) • δ) x
    have hsx : e.symm x = x + (δ x : K) • w := by
      apply e.injective
      simp [e, LinearMap.transvection.apply, hδ, mul_comm]
    rw [hsx]
    simp [mul_comm]
  · change e u = u - (δ u : K) • w
    simp [e, LinearMap.transvection.apply, sub_eq_add_neg]

/-- In the split hyperbolic form, the pair generator built from `(-(f + δ), w)` and `(-f, w)`
has an explicit coordinate action on arbitrary `(d, u)`. This packages the basic hyperbolic
transvection pattern behind the remaining split-rank surjectivity theorem. -/
theorem spinSpecialOrthogonalPairGenerator_apply_dualProd
    (f δ : Module.Dual K W) (w : W) (hf : f w = 1) (hδ : δ w = 0)
    (d : Module.Dual K W) (u : W) :
    (spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
        (-(f + δ), w) (-f, w)
        (by simp [QuadraticForm.dualProd, hf, hδ])
        (by simp [QuadraticForm.dualProd, hf])).1
        (d, u) =
      (d + ((d w - f u) : K) • δ + (δ u : K) • (f + δ), u - (δ u : K) • w) := by
  have hsum : (f + δ) w = 1 := by
    simp [hf, hδ]
  rw [coe_spinSpecialOrthogonalPairGenerator, QuadraticMap.IsometryEquiv.mul_apply,
    pinIsometryRepresentation_apply, pinIsometryEquiv_apply,
    pinIsometryRepresentation_apply, pinIsometryEquiv_apply]
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one (f := f) (w := w) hf
    (d := d) (u := u)]
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one
    (f := f + δ) (w := w) hsum
    (d := ((d w - f u : K) • f - d)) (u := (-(d w - f u : K) • w - u))]
  apply Prod.ext
  · ext x
    simp [hf, hδ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    ring
  · have hcoef : (f u + (-δ u + -d w) : K) - (f u + -d w) = -(δ u) := by
      ring
    simp [hf, hδ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      (f u + (-δ u + -d w)) • w + -((f u + -d w) • w)
          = ((f u + (-δ u + -d w) : K) - (f u + -d w)) • w := by
              simp [sub_eq_add_neg, add_smul]
      _ = -(δ u) • w := by rw [hcoef]
      _ = -(δ u • w) := by simp

/-- In the split hyperbolic form, the pair generator built from `(-(f + δ), w)` and `(-f, w)`
acts on the primal vector `(0, w)` by adding the dual correction `-δ`. This is the basic
hyperbolic transvection pattern behind the remaining split-rank surjectivity theorem. -/
theorem spinSpecialOrthogonalPairGenerator_apply_dualProd_primal_transvection
    (f δ : Module.Dual K W) (w : W) (hf : f w = 1) (hδ : δ w = 0) :
    (spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
        (-(f + δ), w) (-f, w)
        (by simp [QuadraticForm.dualProd, hf, hδ])
        (by simp [QuadraticForm.dualProd, hf])).1
        (0, w) =
      (-δ, w) := by
  rw [spinSpecialOrthogonalPairGenerator_apply_dualProd
    (f := f) (δ := δ) (w := w) hf hδ (d := 0) (u := w)]
  ext <;> simp [hf, hδ]

/-- The same split pair generator sends the dual vector `(-f, 0)` to the shifted dual vector
`(-(f + δ), 0)`. -/
theorem spinSpecialOrthogonalPairGenerator_apply_dualProd_dual_transvection
    (f δ : Module.Dual K W) (w : W) (hf : f w = 1) (hδ : δ w = 0) :
    (spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
        (-(f + δ), w) (-f, w)
        (by simp [QuadraticForm.dualProd, hf, hδ])
        (by simp [QuadraticForm.dualProd, hf])).1
        (-f, 0) =
      (-(f + δ), 0) := by
  rw [spinSpecialOrthogonalPairGenerator_apply_dualProd
    (f := f) (δ := δ) (w := w) hf hδ (d := -f) (u := 0)]
  ext <;> simp [hf, add_comm]

end DualProd

end Field

section DualProdLine

variable {K : Type*} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
private theorem dualMap_eq_smul_id (d : Module.Dual K K) :
    d = (d 1) • (LinearMap.id : Module.Dual K K) := by
  apply LinearMap.ext
  intro y
  calc
    d y = d (y • (1 : K)) := by simp
    _ = y • d 1 := by rw [d.map_smul]
    _ = d 1 * y := by simp [smul_eq_mul, mul_comm]

omit [Invertible (2 : K)] in
private noncomputable def dualLineCoordEquiv : Module.Dual K K ≃ₗ[K] K where
  toFun d := d 1
  invFun a := a • (LinearMap.id : Module.Dual K K)
  left_inv d := by
    simpa using (dualMap_eq_smul_id (K := K) d).symm
  right_inv a := by
    simp
  map_add' d e := by
    simp
  map_smul' a d := by
    simp [smul_eq_mul, mul_comm]

omit [Invertible (2 : K)] in
private noncomputable def dualProdLineCoordEquiv :
    (Module.Dual K K × K) ≃ₗ[K] (K × K) :=
  LinearEquiv.prodCongr (dualLineCoordEquiv (K := K)) (LinearEquiv.refl K K)

omit [Invertible (2 : K)] in
private theorem dualProdLineCoordEquiv_symm_quadratic (x : K × K) :
    QuadraticForm.dualProd K K ((dualProdLineCoordEquiv (K := K)).symm x) = x.1 * x.2 := by
  rcases x with ⟨a, u⟩
  change ((a • (LinearMap.id : Module.Dual K K)) u) = a * u
  simp [smul_eq_mul]

/-- On the split hyperbolic line `K* × K`, the norm-`-1` reflection attached to the vector
`(-a⁻¹, a)` has an explicit coordinate formula. -/
theorem pinLinearRepresentation_apply_iota_of_dualProd_line
    (a : Kˣ) (d : Module.Dual K K) (u : K) :
    pinLinearRepresentation (Q := QuadraticForm.dualProd K K)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K K)
          (-(((a : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (a : K))
          (by simp [QuadraticForm.dualProd]))
        (d, u) =
      (-((u / ((a : K) ^ 2)) : K) • (LinearMap.id : Module.Dual K K), -((a : K) ^ 2) * d 1) := by
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one
    (K := K) (W := K) (f := ((a : K)⁻¹) • (LinearMap.id : Module.Dual K K))
    (w := (a : K)) (by simp) (d := d) (u := u)]
  have hd : ∀ x : K, d x = d 1 * x := by
    intro x
    have h := congrArg (fun e : Module.Dual K K => e x) (dualMap_eq_smul_id (K := K) d)
    simpa [LinearMap.id_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  apply Prod.ext
  · apply LinearMap.ext
    intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
      div_eq_mul_inv]
    rw [hd (a : K), hd y]
    field_simp [a.ne_zero]
    ring
  · rw [hd (a : K)]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    field_simp [a.ne_zero]
    ring

/-- Every split line pair generator acts by a square scalar on the primal line and the inverse
square on the dual line. -/
theorem spinSpecialOrthogonalPairGenerator_apply_dualProd_line
    (a b : Kˣ) (d : Module.Dual K K) (u : K) :
    (spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K K)
        (-(((a : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (a : K))
        (-(((b : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (b : K))
        (by simp [QuadraticForm.dualProd])
        (by simp [QuadraticForm.dualProd])).1 (d, u) =
      ((((b : K) / a) ^ 2 : K) • d, (((a : K) / b) ^ 2 : K) * u) := by
  rw [coe_spinSpecialOrthogonalPairGenerator, QuadraticMap.IsometryEquiv.mul_apply,
    pinIsometryRepresentation_apply, pinIsometryEquiv_apply]
  have hfirst :
      ((pinIsometryRepresentation (Q := QuadraticForm.dualProd K K))
          (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K K)
            (-(((b : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (b : K))
            (by simp [QuadraticForm.dualProd]))) (d, u) =
        (-((u / ((b : K) ^ 2)) : K) • (LinearMap.id : Module.Dual K K), -((b : K) ^ 2) * d 1) := by
    simpa [pinIsometryRepresentation_apply, pinIsometryEquiv_apply] using
      (pinLinearRepresentation_apply_iota_of_dualProd_line (K := K) (a := b) (d := d) (u := u))
  rw [hfirst]
  rw [pinLinearRepresentation_apply_iota_of_dualProd_line (K := K) (a := a)
    (d := -((u / ((b : K) ^ 2)) : K) • (LinearMap.id : Module.Dual K K))
    (u := -((b : K) ^ 2) * d 1)]
  have hd : ∀ x : K, d x = d 1 * x := by
    intro x
    have h := congrArg (fun e : Module.Dual K K => e x) (dualMap_eq_smul_id (K := K) d)
    simpa [LinearMap.id_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  apply Prod.ext
  · apply LinearMap.ext
    intro y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, div_eq_mul_inv]
    rw [hd y]
    field_simp [a.ne_zero, b.ne_zero]
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, div_eq_mul_inv]
    field_simp [a.ne_zero, b.ne_zero]

/-- On the split hyperbolic line, the determinant-one transport of a scalar unit acts by the
inverse scalar on the dual coordinate and by the scalar itself on the primal coordinate. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit
    (a : Kˣ) (d : Module.Dual K K) (u : K) :
    (dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit a)).1 (d, u) =
      (((a : K)⁻¹) • d, (a : K) * u) := by
  rw [coe_dualProdSpecialOrthogonalOfLinearEquiv]
  change (((LinearEquiv.smulOfUnit a).dualMap.symm d), (LinearEquiv.smulOfUnit a u)) =
    (((a : K)⁻¹) • d, (a : K) * u)
  apply Prod.ext
  · apply LinearMap.ext
    intro y
    rw [show ((LinearEquiv.smulOfUnit a).dualMap.symm d) y = d ((↑a)⁻¹ * y) by
      simp [LinearEquiv.smulOfUnit, Units.smul_def, Units.val_inv_eq_inv_val]]
    rw [show ((((a : K)⁻¹) • d) y) = (↑a)⁻¹ * d y by
      simp [smul_eq_mul]]
    simpa [smul_eq_mul] using d.map_smul ((↑a)⁻¹) y
  · rfl

/-- A split line pair generator is exactly the square-scaling element determined by the ratio of
its two unit parameters. -/
theorem spinSpecialOrthogonalPairGenerator_dualProd_line_eq_squareScaling
    (a b : Kˣ) :
    spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K K)
        (-(((a : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (a : K))
        (-(((b : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (b : K))
        (by simp [QuadraticForm.dualProd])
        (by simp [QuadraticForm.dualProd]) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
        (LinearEquiv.smulOfUnit ((a / b) ^ 2)) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rcases x with ⟨d, u⟩
  rw [spinSpecialOrthogonalPairGenerator_apply_dualProd_line (K := K) (a := a) (b := b) (d := d)
    (u := u)]
  rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := (a / b) ^ 2)
    (d := d) (u := u)]
  apply Prod.ext
  · apply LinearMap.ext
    intro y
    simp [smul_eq_mul, div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]
  · simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]

omit [Invertible (2 : K)] in
/-- A norm-`-1` vector in the split hyperbolic line is determined by a nonzero primal coordinate
and the matching inverse dual scalar. -/
theorem dualProd_line_eq_neg_inv_smul_id_of_eq_neg_one
    {d : Module.Dual K K} {u : K} (h : QuadraticForm.dualProd K K (d, u) = -1) :
    u ≠ 0 ∧ d = -(u⁻¹ • (LinearMap.id : Module.Dual K K)) := by
  have hd : ∀ x : K, d x = d 1 * x := by
    intro x
    have h' := congrArg (fun e : Module.Dual K K => e x) (dualMap_eq_smul_id (K := K) d)
    simpa [LinearMap.id_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h'
  have hu : u ≠ 0 := by
    intro hu0
    have hzero : (0 : K) ≠ -1 := by simp
    exact hzero (by simpa [QuadraticForm.dualProd, hu0] using h)
  have hdu : d 1 * u = -1 := by
    have hdu' : d u = -1 := by
      simpa [QuadraticForm.dualProd] using h
    rw [hd u] at hdu'
    exact hdu'
  have hd1 : d 1 = -u⁻¹ := by
    have hmul : d 1 * u = (-u⁻¹ : K) * u := by
      calc
      d 1 * u = -1 := hdu
      _ = (-u⁻¹ : K) * u := by
        field_simp [hu]
    exact mul_right_cancel₀ hu hmul
  refine ⟨hu, ?_⟩
  calc
    d = (-u⁻¹ : K) • (LinearMap.id : Module.Dual K K) := by
      simpa [hd1] using dualMap_eq_smul_id (K := K) d
    _ = -(u⁻¹ • (LinearMap.id : Module.Dual K K)) := by
      ext x
      simp [smul_eq_mul]

/-- Every split line pair generator belongs to the square-scaling family. -/
theorem spinSpecialOrthogonalPairGenerator_eq_squareScaling_of_dualProd_line
    {d₁ d₂ : Module.Dual K K} {u₁ u₂ : K}
    (h₁ : QuadraticForm.dualProd K K (d₁, u₁) = -1)
    (h₂ : QuadraticForm.dualProd K K (d₂, u₂) = -1) :
    ∃ t : Kˣ,
      spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K K)
          (d₁, u₁) (d₂, u₂) h₁ h₂ =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
          (LinearEquiv.smulOfUnit (t ^ 2)) := by
  obtain ⟨hu₁, hd₁⟩ := dualProd_line_eq_neg_inv_smul_id_of_eq_neg_one (K := K) (d := d₁)
    (u := u₁) h₁
  obtain ⟨hu₂, hd₂⟩ := dualProd_line_eq_neg_inv_smul_id_of_eq_neg_one (K := K) (d := d₂)
    (u := u₂) h₂
  let a : Kˣ := Units.mk0 u₁ hu₁
  let b : Kˣ := Units.mk0 u₂ hu₂
  refine ⟨a / b, ?_⟩
  subst d₁ d₂
  have h₁canon :
      h₁ =
        (by
          simp [QuadraticForm.dualProd, hu₁] :
          QuadraticForm.dualProd K K (-(u₁⁻¹ • (LinearMap.id : Module.Dual K K)), u₁) = -1) :=
    Subsingleton.elim _ _
  have h₂canon :
      h₂ =
        (by
          simp [QuadraticForm.dualProd, hu₂] :
          QuadraticForm.dualProd K K (-(u₂⁻¹ • (LinearMap.id : Module.Dual K K)), u₂) = -1) :=
    Subsingleton.elim _ _
  cases h₁canon
  cases h₂canon
  simpa [a, b] using
    (spinSpecialOrthogonalPairGenerator_dualProd_line_eq_squareScaling (K := K) (a := a)
      (b := b))

/-- Scalar multiplication on the split hyperbolic line gives a packaged one-parameter subgroup of
`SO(1,1)`. -/
noncomputable def dualProdLineScalingHom :
    Kˣ →* (QuadraticForm.dualProd K K).specialOrthogonalGroup where
  toFun t :=
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit t)
  map_one' := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    rcases x with ⟨d, u⟩
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := 1) (d := d) (u := u)]
    simp
  map_mul' t s := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    rcases x with ⟨d, u⟩
    change (dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
        (LinearEquiv.smulOfUnit (t * s))).1 (d, u) =
      ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit t)).1 *
        (dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit s)).1)
        (d, u)
    rw [QuadraticMap.IsometryEquiv.mul_apply]
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := s) (d := d) (u := u)]
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := t)
      (d := ((↑s : K)⁻¹) • d) (u := (s : K) * u)]
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := t * s)
      (d := d) (u := u)]
    apply Prod.ext
    · apply LinearMap.ext
      intro y
      simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    · simp [mul_assoc, mul_comm, mul_left_comm]

/-- The split-line scaling family is faithful: the scalar is recovered from the action on the
primal basis vector. -/
theorem dualProdLineScalingHom_injective :
    Function.Injective (dualProdLineScalingHom (K := K)) := by
  intro t s h
  have hscaling :
      dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit t) =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K) (LinearEquiv.smulOfUnit s) := by
    simpa [dualProdLineScalingHom] using h
  have hsnd : (t : K) = (s : K) := by
    have h' :=
      congrArg
        (fun g : (QuadraticForm.dualProd K K).specialOrthogonalGroup =>
          Prod.snd (g.1 (0, (1 : K)))) hscaling
    change Prod.snd ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
        (LinearEquiv.smulOfUnit t)).1 (0, (1 : K))) =
      Prod.snd ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
        (LinearEquiv.smulOfUnit s)).1 (0, (1 : K))) at h'
    have ht_eval :
        Prod.snd ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
          (LinearEquiv.smulOfUnit t)).1 (0, (1 : K))) = (t : K) := by
      rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := t) (d := 0)
        (u := 1)]
      simp
    have hs_eval :
        Prod.snd ((dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := K)
          (LinearEquiv.smulOfUnit s)).1 (0, (1 : K))) = (s : K) := by
      rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit (K := K) (a := s) (d := 0)
        (u := 1)]
      simp
    rw [ht_eval, hs_eval] at h'
    exact h'
  exact Units.ext hsnd

/-- The split-line scaling family exhausts `SO(1,1)`: every determinant-one isometry preserves the
two isotropic lines and is uniquely determined by its scalar on the primal line. -/
theorem dualProdLineScalingHom_surjective :
    Function.Surjective (dualProdLineScalingHom (K := K)) := by
  intro g
  let coord : (Module.Dual K K × K) ≃ₗ[K] (K × K) := dualProdLineCoordEquiv (K := K)
  let glin : (Module.Dual K K × K) ≃ₗ[K] (Module.Dual K K × K) :=
    ((g : (QuadraticForm.dualProd K K).IsometryEquiv (QuadraticForm.dualProd K K)).toLinearEquiv :
      (Module.Dual K K × K) ≃ₗ[K] (Module.Dual K K × K))
  let h : (K × K) ≃ₗ[K] (K × K) := (coord.symm.trans glin).trans coord
  let p : K × K := h (1, 0)
  let q : K × K := h (0, 1)
  have h_preserves (x : K × K) : (h x).1 * (h x).2 = x.1 * x.2 := by
    have hmap :
        QuadraticForm.dualProd K K (glin (coord.symm x)) =
          QuadraticForm.dualProd K K (coord.symm x) := by
      simpa [glin] using
        (g : (QuadraticForm.dualProd K K).IsometryEquiv (QuadraticForm.dualProd K K)).map_app
          (coord.symm x)
    have hcoord : coord.symm (h x) = glin (coord.symm x) := by
      apply coord.injective
      simp [h]
    calc
      (h x).1 * (h x).2 = QuadraticForm.dualProd K K (coord.symm (h x)) := by
        symm
        exact dualProdLineCoordEquiv_symm_quadratic (K := K) (h x)
      _ = QuadraticForm.dualProd K K (glin (coord.symm x)) := by
        rw [hcoord]
      _ = QuadraticForm.dualProd K K (coord.symm x) := hmap
      _ = x.1 * x.2 := dualProdLineCoordEquiv_symm_quadratic (K := K) x
  have hdet : LinearEquiv.det h = 1 := by
    calc
      LinearEquiv.det h = LinearEquiv.det glin := by
        simpa [h] using (LinearEquiv.det_conj glin coord)
      _ = 1 := by
        simpa [glin] using QuadraticForm.det_eq_one (Q := QuadraticForm.dualProd K K) g
  have h_apply (x : K × K) :
      h x = (p.1 * x.1 + q.1 * x.2, p.2 * x.1 + q.2 * x.2) := by
    rcases x with ⟨x₁, x₂⟩
    have hx : ((x₁, x₂) : K × K) = x₁ • ((1, 0) : K × K) + x₂ • ((0, 1) : K × K) := by
      ext <;> simp [smul_eq_mul, mul_comm]
    rw [hx, map_add, map_smul, map_smul]
    ext <;> simp [p, q, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  have hp_iso : p.1 * p.2 = 0 := by
    simpa [p] using h_preserves ((1, 0) : K × K)
  have hq_iso : q.1 * q.2 = 0 := by
    simpa [q] using h_preserves ((0, 1) : K × K)
  have hsum : p.1 * q.2 + q.1 * p.2 = 1 := by
    have h11 : (p.1 + q.1) * (p.2 + q.2) = 1 := by
      have h11' : (h ((1, 1) : K × K)).1 * (h ((1, 1) : K × K)).2 = 1 := by
        simpa using h_preserves ((1, 1) : K × K)
      have hh11 : h ((1, 1) : K × K) = (p.1 + q.1, p.2 + q.2) := by
        simpa [p, q] using h_apply ((1, 1) : K × K)
      rw [hh11] at h11'
      exact h11'
    calc
      p.1 * q.2 + q.1 * p.2 = (p.1 + q.1) * (p.2 + q.2) := by
        symm
        calc
          (p.1 + q.1) * (p.2 + q.2) = p.1 * p.2 + p.1 * q.2 + (q.1 * p.2 + q.1 * q.2) := by
            ring
          _ = p.1 * q.2 + q.1 * p.2 := by
            rw [hp_iso, hq_iso]
            ring
      _ = 1 := h11
  have hdet_matrix : p.1 * q.2 - q.1 * p.2 = 1 := by
    let h' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
      ((LinearEquiv.finTwoArrow K K).trans h).trans (LinearEquiv.finTwoArrow K K).symm
    have hdet' : LinearEquiv.det h' = 1 := by
      simpa [h'] using (LinearEquiv.det_conj h (LinearEquiv.finTwoArrow K K).symm).trans hdet
    have hdet_lin : LinearMap.det (h' : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = (1 : K) := by
      simpa [LinearEquiv.coe_det] using congrArg (fun u : Kˣ => (u : K)) hdet'
    have hmat :
        LinearMap.toMatrix' (h' : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = !![p.1, q.1; p.2, q.2] := by
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix'_apply, h', h_apply, LinearEquiv.finTwoArrow]
    rw [← LinearMap.det_toMatrix' (h' : (Fin 2 → K) →ₗ[K] (Fin 2 → K)), hmat,
      Matrix.det_fin_two] at hdet_lin
    exact hdet_lin
  have hcross_zero : q.1 * p.2 = 0 := by
    have htwo : (2 : K) * (q.1 * p.2) = 0 := by
      calc
        (2 : K) * (q.1 * p.2) = (p.1 * q.2 + q.1 * p.2) - (p.1 * q.2 - q.1 * p.2) := by
          ring
        _ = 0 := by
          rw [hsum, hdet_matrix]
          ring
    exact (mul_eq_zero.mp htwo).resolve_left ((isUnit_of_invertible (2 : K)).ne_zero)
  have hpq_one : p.1 * q.2 = 1 := by
    calc
      p.1 * q.2 = p.1 * q.2 + q.1 * p.2 := by rw [hcross_zero, add_zero]
      _ = 1 := hsum
  have hp1_ne : p.1 ≠ 0 := by
    intro hp1_zero
    have : (0 : K) = 1 := by
      simpa [hp1_zero] using hpq_one
    exact zero_ne_one this
  have hq2_ne : q.2 ≠ 0 := by
    intro hq2_zero
    have : (0 : K) = 1 := by
      simpa [hq2_zero] using hpq_one
    exact zero_ne_one this
  have hp2_zero : p.2 = 0 := by
    rcases mul_eq_zero.mp hp_iso with hp1_zero | hp2_zero
    · exact False.elim (hp1_ne hp1_zero)
    · exact hp2_zero
  have hq1_zero : q.1 = 0 := by
    rcases mul_eq_zero.mp hq_iso with hq1_zero | hq2_zero
    · exact hq1_zero
    · exact False.elim (hq2_ne hq2_zero)
  let t : Kˣ := Units.mk0 q.2 hq2_ne
  have hp1_inv : p.1 = ((t : K)⁻¹) := by
    apply mul_right_cancel₀ t.ne_zero
    calc
      p.1 * (t : K) = 1 := by
        simpa [t] using hpq_one
      _ = ((t : K)⁻¹) * (t : K) := by
        exact (inv_mul_cancel₀ t.ne_zero).symm
  have hdual :
      g.1 ((LinearMap.id : Module.Dual K K), 0) =
        (((t : K)⁻¹) • (LinearMap.id : Module.Dual K K), 0) := by
    have hcoord_id : coord.symm ((1, 0) : K × K) = ((LinearMap.id : Module.Dual K K), 0) := by
      apply Prod.ext
      · apply LinearMap.ext
        intro y
        change ((dualLineCoordEquiv (K := K)).symm 1) y = (LinearMap.id : Module.Dual K K) y
        simp [dualLineCoordEquiv, smul_eq_mul]
      · change (LinearEquiv.refl K K).symm 0 = (0 : K)
        simp
    have hdual_coord : coord (g.1 ((LinearMap.id : Module.Dual K K), 0)) = p := by
      calc
        coord (g.1 ((LinearMap.id : Module.Dual K K), 0)) =
            coord (g.1 (coord.symm ((1, 0) : K × K))) := by
              rw [hcoord_id.symm]
        _ = p := by
              change coord (glin (coord.symm ((1, 0) : K × K))) = p
              simpa [h, p]
    have hdual_eval : (g.1 ((LinearMap.id : Module.Dual K K), 0)).1 1 = (t : K)⁻¹ := by
      have := congrArg Prod.fst hdual_coord
      simpa [p, hp1_inv] using this
    have hdual_second : (g.1 ((LinearMap.id : Module.Dual K K), 0)).2 = 0 := by
      have := congrArg Prod.snd hdual_coord
      simpa [p, hp2_zero] using this
    apply Prod.ext
    · calc
        (g.1 ((LinearMap.id : Module.Dual K K), 0)).1 =
            ((g.1 ((LinearMap.id : Module.Dual K K), 0)).1 1) •
              (LinearMap.id : Module.Dual K K) := by
              symm
              exact (dualMap_eq_smul_id (K := K) (g.1 ((LinearMap.id : Module.Dual K K), 0)).1).symm
        _ = ((t : K)⁻¹) • (LinearMap.id : Module.Dual K K) := by
              rw [hdual_eval]
    · exact hdual_second
  have hprimal : g.1 (0, (1 : K)) = (0, (t : K)) := by
    have hcoord_primal : coord.symm ((0, 1) : K × K) = (0, (1 : K)) := by
      apply Prod.ext
      · apply LinearMap.ext
        intro y
        change ((dualLineCoordEquiv (K := K)).symm 0) y = (0 : K)
        simp [dualLineCoordEquiv, smul_eq_mul]
      · change (LinearEquiv.refl K K).symm 1 = (1 : K)
        simp
    have hprimal_coord : coord (g.1 (0, (1 : K))) = q := by
      calc
        coord (g.1 (0, (1 : K))) = coord (g.1 (coord.symm ((0, 1) : K × K))) := by
          rw [hcoord_primal.symm]
        _ = q := by
          change coord (glin (coord.symm ((0, 1) : K × K))) = q
          simpa [h, q]
    have hprimal_eval : (g.1 (0, (1 : K))).1 1 = 0 := by
      have := congrArg Prod.fst hprimal_coord
      simpa [q, hq1_zero] using this
    have hprimal_second : (g.1 (0, (1 : K))).2 = (t : K) := by
      have := congrArg Prod.snd hprimal_coord
      simpa [q, t] using this
    apply Prod.ext
    · calc
        (g.1 (0, (1 : K))).1 = ((g.1 (0, (1 : K))).1 1) • (LinearMap.id : Module.Dual K K) := by
          symm
          exact (dualMap_eq_smul_id (K := K) (g.1 (0, (1 : K))).1).symm
        _ = 0 := by
          rw [hprimal_eval]
          simp
    · exact hprimal_second
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rcases x with ⟨d, u⟩
  have hx :
      (d, u) = (d 1) • ((LinearMap.id : Module.Dual K K), (0 : K)) + u • (0, (1 : K)) := by
    apply Prod.ext
    · simpa using dualMap_eq_smul_id (K := K) d
    · simp
  have hxy : g.1 (d, u) = (dualProdLineScalingHom (K := K) t).1 (d, u) := by
    calc
      g.1 (d, u) = g.1 ((d 1) • ((LinearMap.id : Module.Dual K K), (0 : K)) + u • (0, (1 : K))) := by
        rw [hx]
      _ = (d 1) • g.1 ((LinearMap.id : Module.Dual K K), 0) + u • g.1 (0, (1 : K)) := by
        rw [map_add, map_smul, map_smul]
      _ = (d 1) • ((((t : K)⁻¹) • (LinearMap.id : Module.Dual K K)), 0) + u • (0, (t : K)) := by
        rw [hdual, hprimal]
      _ = (((t : K)⁻¹) • d, (t : K) * u) := by
        apply Prod.ext
        · rw [dualMap_eq_smul_id (K := K) d]
          ext y
          simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
        · simp [smul_eq_mul, mul_comm]
      _ = (dualProdLineScalingHom (K := K) t).1 (d, u) := by
        simpa [dualProdLineScalingHom] using
          (dualProdSpecialOrthogonalOfLinearEquiv_apply_smulOfUnit
            (K := K) (a := t) (d := d) (u := u)).symm
  simpa using hxy.symm

/-- The square-scaling subgroup of the split hyperbolic line. Every canonical pair generator lands
here. -/
noncomputable def dualProdLineSquareScalingSubgroup :
    Subgroup ((QuadraticForm.dualProd K K).specialOrthogonalGroup) :=
  MonoidHom.range ((dualProdLineScalingHom (K := K)).comp (powMonoidHom (α := Kˣ) 2))

/-- On the split hyperbolic line, every canonical pair generator is a square scaling. -/
theorem spinSpecialOrthogonalPairGeneratorSet_dualProdLine_subset_squareScalingSubgroup :
    spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K) ⊆
      dualProdLineSquareScalingSubgroup (K := K) := by
  rintro _ ⟨p, rfl⟩
  rcases spinSpecialOrthogonalPairGenerator_eq_squareScaling_of_dualProd_line
      (K := K) (h₁ := p.2.1) (h₂ := p.2.2) with ⟨t, ht⟩
  exact ⟨t, by
    simpa [dualProdLineSquareScalingSubgroup, dualProdLineScalingHom] using ht.symm⟩

/-- Hence the subgroup generated by the split-line pair generators is contained in the square
scaling subgroup. -/
theorem spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_le_squareScalingSubgroup :
    Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) ≤
      dualProdLineSquareScalingSubgroup (K := K) := by
  rw [Subgroup.closure_le]
  exact spinSpecialOrthogonalPairGeneratorSet_dualProdLine_subset_squareScalingSubgroup (K := K)

/-- Conversely, every split-line square scaling is already a canonical pair generator, so the
generated subgroup is exactly the square-scaling subgroup. -/
theorem dualProdLineSquareScalingSubgroup_le_pairGeneratorClosure :
    dualProdLineSquareScalingSubgroup (K := K) ≤
      Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) := by
  rintro _ ⟨t, rfl⟩
  let p :
      {ab : ((Module.Dual K K × K) × (Module.Dual K K × K)) //
          QuadraticForm.dualProd K K ab.1 = -1 ∧ QuadraticForm.dualProd K K ab.2 = -1} :=
    ⟨(((-(((t : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (t : K))),
        (-((((1 : Kˣ) : K)⁻¹) • (LinearMap.id : Module.Dual K K)), (1 : K))),
      by
        simp [QuadraticForm.dualProd, t.ne_zero]⟩
  exact Subgroup.subset_closure ⟨p, by
    simpa [p, dualProdLineScalingHom] using
      (spinSpecialOrthogonalPairGenerator_dualProd_line_eq_squareScaling (K := K) (a := t)
        (b := 1))⟩

/-- The split-line subgroup generated by canonical pair generators is exactly the square-scaling
subgroup. -/
theorem spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_squareScalingSubgroup :
    Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) =
      dualProdLineSquareScalingSubgroup (K := K) := by
  apply le_antisymm
  · exact spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_le_squareScalingSubgroup (K := K)
  · exact dualProdLineSquareScalingSubgroup_le_pairGeneratorClosure (K := K)

/-- If every unit is a square, then the split-line pair generators do generate `SO(1,1)`. -/
theorem dualProdLineSquareScalingSubgroup_eq_top_of_square_surjective
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2)) :
    dualProdLineSquareScalingSubgroup (K := K) = ⊤ := by
  apply le_antisymm le_top
  intro g hg
  rcases dualProdLineScalingHom_surjective (K := K) g with ⟨t, rfl⟩
  rcases hsq t with ⟨s, hs⟩
  exact ⟨s, by
    simpa [dualProdLineSquareScalingSubgroup, dualProdLineScalingHom] using
      congrArg (dualProdLineScalingHom (K := K)) hs⟩

/-- Hence over fields whose unit group is entirely squares, the split-line pair generators recover
all of `SO(1,1)`. -/
theorem spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_top_of_square_surjective
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2)) :
    Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) =
      (⊤ : Subgroup ((QuadraticForm.dualProd K K).specialOrthogonalGroup)) := by
  rw [spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_squareScalingSubgroup]
  exact dualProdLineSquareScalingSubgroup_eq_top_of_square_surjective (K := K) hsq

/-- Under surjectivity of the square map on `Kˣ`, the ambient spin action on the split hyperbolic
line is surjective onto `SO(1,1)`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_of_square_surjective
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2)) :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) := by
  apply spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top
  exact spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_top_of_square_surjective
    (K := K) hsq

/-- A nonsquare split-line scaling does not lie in the subgroup generated by canonical pair
generators. -/
theorem dualProdLineScalingHom_not_mem_squareScalingSubgroup {u : Kˣ}
    (hu : u ∉ MonoidHom.range (powMonoidHom (α := Kˣ) 2)) :
    dualProdLineScalingHom (K := K) u ∉ dualProdLineSquareScalingSubgroup (K := K) := by
  rintro ⟨t, ht⟩
  apply hu
  refine ⟨t, ?_⟩
  apply dualProdLineScalingHom_injective (K := K)
  simpa [dualProdLineSquareScalingSubgroup, dualProdLineScalingHom] using ht

/-- If `Kˣ` has a unit outside the square map, then the canonical pair generators do not generate
`SO(1,1)` on the split hyperbolic line. This refutes the current generator route in split rank
one over such fields. -/
theorem spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_ne_top_of_exists_nonsquare_unit
    (hnsq : ∃ u : Kˣ, u ∉ MonoidHom.range (powMonoidHom (α := Kˣ) 2)) :
    Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) ≠
      (⊤ : Subgroup ((QuadraticForm.dualProd K K).specialOrthogonalGroup)) := by
  rcases hnsq with ⟨u, hu⟩
  intro htop
  have hmem :
      dualProdLineScalingHom (K := K) u ∈
        Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := QuadraticForm.dualProd K K)) := by
    simpa [htop]
  exact (dualProdLineScalingHom_not_mem_squareScalingSubgroup (K := K) hu)
    ((spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_le_squareScalingSubgroup
      (K := K)) hmem)

end DualProdLine

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
