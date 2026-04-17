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
* `Spinor.pinConjAlgEquiv`, `Spinor.spinConjAlgEquiv` — Clifford conjugation by a pin/spin
  element as an algebra automorphism.
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
* `Spinor.spinSpecialOrthogonalRepresentation` — once the determinant-one step is supplied, the
  ambient isometry representation factors through `QuadraticForm.specialOrthogonalGroup Q`.
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
