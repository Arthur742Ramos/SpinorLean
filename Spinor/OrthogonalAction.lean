/-
  Ambient spin-group action on the underlying quadratic module.
-/

import Spinor.SpinRep
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Finset.NoncommProd
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Pi
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
* `Spinor.lipschitzConjAlgEquiv_eq_refl_of_lipschitzLinearRepresentation_eq_one` and
  `Spinor.commute_of_lipschitzLinearRepresentation_eq_one` — Lipschitz linear-kernel elements
  act trivially by Clifford conjugation and commute with every Clifford element.
* `Spinor.lipschitzLinearRepresentation_gradedDetParity` and
  `Spinor.lipschitzLinearRepresentation_mem_even_of_eq_one_of_det_ne` — Lipschitz elements have
  even/odd Clifford parity compatible with the determinant of the ambient action, excluding odd
  linear-kernel lifts when the odd determinant branch is not `1`.
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
* `Spinor.spinIsometryRepresentation_not_surjective_of_exists_det_ne_one` — if the full
  orthogonal group contains an isometry with determinant different from `1`, then the ambient spin
  map is not surjective onto that full target.
* `Spinor.pinIsometryRepresentation_det_of_quadratic_eq_neg_one` and
  `Spinor.spinIsometryRepresentation_not_surjective_of_exists_quadratic_eq_neg_one_of_det_ne` —
  the corresponding concrete obstruction supplied by a norm-`-1` pin generator when its determinant
  branch is nontrivial.
* `Spinor.spinSpecialOrthogonalRepresentation`,
  `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional` — the ambient isometry
  representation factors through `QuadraticForm.specialOrthogonalGroup Q`, either from an external
  determinant hypothesis or canonically in the finite-dimensional field setting.
* `Spinor.spinIsometryRepresentation_range_eq_map_specialOrthogonalRepresentationFiniteDimensional`
  — the full-isometry image is exactly the subtype image of the special-orthogonal spin map.
* `Spinor.pinIotaOfQuadraticEqNegOne`, `Spinor.spinIotaPairOfQuadraticEqNegOne`,
  `Spinor.spinSpecialOrthogonalPairGenerator` — canonical pin/spin lifts of norm-`-1` vector
  reflections and their paired special-orthogonal images.
* `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top`
  — surjectivity of the ambient spin covering map reduces to showing those paired generators span
  `SO(V,Q)`.
* `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective`
  and
  `Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional_not_surjective_dualProdLine_of_exists_nonsquare_unit`
  — the exact split-line criterion: the spin map onto `SO(1,1)` is surjective precisely when every
  unit of the base field is a square, and it is not surjective in the presence of a nonsquare unit.
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

/-- A Lipschitz linear-kernel element acts trivially on the full Clifford algebra by conjugation. -/
theorem lipschitzConjAlgEquiv_eq_refl_of_lipschitzLinearRepresentation_eq_one
    (x : lipschitzGroup Q) (hx : lipschitzLinearRepresentation (Q := Q) x = 1) :
    lipschitzConjAlgEquiv (Q := Q) x = AlgEquiv.refl := by
  ext a
  have hhom :
      (lipschitzConjAlgEquiv (Q := Q) x).toAlgHom =
        (AlgEquiv.refl : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q).toAlgHom := by
    refine CliffordAlgebra.hom_ext ?_
    ext m
    have hm : lipschitzLinearEquiv (Q := Q) x m = m := by
      simpa [lipschitzLinearRepresentation_apply] using
        congrArg (fun e : M ≃ₗ[R] M => e m) hx
    simpa [lipschitzConjAlgEquiv_apply, hm] using
      (lipschitzLinearEquiv_ι (Q := Q) x m).symm
  exact congrArg (fun f : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q => f a) hhom

/-- A Lipschitz linear-kernel element commutes with every Clifford element. -/
theorem commute_of_lipschitzLinearRepresentation_eq_one
    (x : lipschitzGroup Q) (hx : lipschitzLinearRepresentation (Q := Q) x = 1)
    (a : CliffordAlgebra Q) :
    Commute (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) a := by
  let u : (CliffordAlgebra Q)ˣ := x
  have hconj : lipschitzConjAlgEquiv (Q := Q) x a = a := by
    simp [lipschitzConjAlgEquiv_eq_refl_of_lipschitzLinearRepresentation_eq_one (Q := Q) x hx]
  have hcomm :
      (u : CliffordAlgebra Q) * a = a * (u : CliffordAlgebra Q) := by
    have hconj' : (u : CliffordAlgebra Q) * a * ↑u⁻¹ = a := by
      simpa [u, lipschitzConjAlgEquiv_apply, ConjAct.toConjAct_smul] using hconj
    rw [Units.mul_inv_eq_iff_eq_mul] at hconj'
    exact hconj'
  simpa [u, Commute] using hcomm

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
the packaged special orthogonal subgroup. Downstream covering statements add either a concrete
generator-closure hypothesis or the exact split-line/Levi image criteria proved in this module
and its dependents. -/
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
`{1, -1}` over a domain. This packages the scalar-reduction step used by the full kernel theorem. -/
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

/-- Graded determinant-parity form of `lipschitzLinearRepresentation_detParity`.

The Clifford value of a Lipschitz element is either even, with determinant `1`, or odd, with
determinant the value of an invertible vector generator. -/
def lipschitzLinearRepresentationGradedDetParity (x : lipschitzGroup Q) : Prop :=
  ((((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      CliffordAlgebra.even Q ∧
    LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) = 1) ∨
  ((((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 1 ∧
    LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) =
      (-1 : Kˣ) ^ (Module.finrank K V - 1))

omit [FiniteDimensional K V] in
theorem lipschitzLinearRepresentationGradedDetParity_mul {x y : lipschitzGroup Q}
    (hx : lipschitzLinearRepresentationGradedDetParity (Q := Q) x)
    (hy : lipschitzLinearRepresentationGradedDetParity (Q := Q) y) :
    lipschitzLinearRepresentationGradedDetParity (Q := Q) (x * y) := by
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
    · change
        lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y ∈ CliffordAlgebra.even Q
      exact (CliffordAlgebra.even Q).mul_mem hx.1 hy.1
    · rw [hdetMul, hx.2, hy.2]
      simp
  · right
    constructor
    · change
        lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y ∈ CliffordAlgebra.evenOdd Q 1
      have hx0 : lipschitzVal (Q := Q) x ∈ CliffordAlgebra.evenOdd Q 0 := by
        simpa [CliffordAlgebra.even] using hx.1
      simpa using SetLike.mul_mem_graded hx0 hy.1
    · rw [hdetMul, hx.2, hy.2]
      simp
  · right
    constructor
    · change
        lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y ∈ CliffordAlgebra.evenOdd Q 1
      have hy0 : lipschitzVal (Q := Q) y ∈ CliffordAlgebra.evenOdd Q 0 := by
        simpa [CliffordAlgebra.even] using hy.1
      simpa [add_comm] using SetLike.mul_mem_graded hx.1 hy0
    · rw [hdetMul, hx.2, hy.2]
      simp
  · left
    constructor
    · change
        lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y ∈ CliffordAlgebra.even Q
      have hxy : lipschitzVal (Q := Q) x * lipschitzVal (Q := Q) y ∈
          CliffordAlgebra.evenOdd Q ((1 : ZMod 2) + 1) :=
        SetLike.mul_mem_graded hx.1 hy.1
      simpa [CliffordAlgebra.even] using hxy
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

/-- Every Lipschitz element has homogeneous Clifford parity compatible with the determinant of
its ambient linear action. -/
theorem lipschitzLinearRepresentation_gradedDetParity (x : lipschitzGroup Q) :
    lipschitzLinearRepresentationGradedDetParity (Q := Q) x := by
  let s : Set (CliffordAlgebra Q)ˣ := ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q))
  let p : (g : (CliffordAlgebra Q)ˣ) → g ∈ Subgroup.closure s → Prop :=
    fun g hg =>
      lipschitzLinearRepresentationGradedDetParity (Q := Q)
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
      right
      constructor
      · change (g : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1
        rw [← ha]
        exact CliffordAlgebra.ι_mem_evenOdd_one (Q := Q) a
      · simpa [p, hg'] using lipschitzLinearRepresentation_det_cliffordIota (Q := Q) a)
    (fun g hg => by
      obtain ⟨a, ha⟩ := hg
      letI := g.invertible
      letI : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
      letI : Invertible (Q a) := CliffordAlgebra.invertibleOfInvertibleι (Q := Q) a
      have hg' : g = cliffordIotaUnit (Q := Q) a := by
        apply Units.ext
        simpa [cliffordIotaUnit] using ha.symm
      right
      constructor
      · change (↑g⁻¹ : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1
        rw [hg']
        change
          lipschitzVal (Q := Q) ((cliffordIotaLipschitz (Q := Q) a)⁻¹) ∈
            CliffordAlgebra.evenOdd Q 1
        rw [coe_cliffordIotaLipschitz_inv (Q := Q) a]
        exact Submodule.smul_mem _ _ (CliffordAlgebra.ι_mem_evenOdd_one (Q := Q) a)
      · have hdetInv :
            LinearEquiv.det
                (lipschitzLinearRepresentation (Q := Q)
                  ((cliffordIotaLipschitz (Q := Q) a)⁻¹)) =
              (LinearEquiv.det
                (lipschitzLinearRepresentation (Q := Q)
                  (cliffordIotaLipschitz (Q := Q) a)))⁻¹ := by
          rw [(lipschitzLinearRepresentation (Q := Q)).map_inv]
          exact map_inv (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ)
            (lipschitzLinearRepresentation (Q := Q) (cliffordIotaLipschitz (Q := Q) a))
        have hdet :
            LinearEquiv.det
                (lipschitzLinearRepresentation (Q := Q)
                  ((cliffordIotaLipschitz (Q := Q) a)⁻¹)) =
              (-1 : Kˣ) ^ (Module.finrank K V - 1) := by
          rw [hdetInv, lipschitzLinearRepresentation_det_cliffordIota (Q := Q) a]
          let n : ℕ := Module.finrank K V - 1
          have hsq : ((-1 : Kˣ) ^ n) * ((-1 : Kˣ) ^ n) = 1 := by
            apply Units.ext
            change (((-1 : K) ^ n) * ((-1 : K) ^ n)) = 1
            rw [← pow_add, ← two_mul n, pow_mul]
            simp
          exact inv_eq_of_mul_eq_one_left hsq
        simpa [p, hg'] using hdet)
    (by
      left
      constructor
      · change (1 : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q
        exact (CliffordAlgebra.even Q).one_mem
      · change LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) (1 : lipschitzGroup Q)) = 1
        rw [(lipschitzLinearRepresentation (Q := Q)).map_one]
        simp)
    (fun g h hg hh hg' hh' => by
      simpa [p] using lipschitzLinearRepresentationGradedDetParity_mul (Q := Q) hg' hh')
    hx

/-- A Lipschitz linear-kernel element is even whenever the odd determinant branch is excluded. -/
theorem lipschitzLinearRepresentation_mem_even_of_eq_one_of_det_ne
    (x : lipschitzGroup Q) (hx : lipschitzLinearRepresentation (Q := Q) x = 1)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1) :
    (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      CliffordAlgebra.even Q := by
  rcases lipschitzLinearRepresentation_gradedDetParity (Q := Q) x with h | h
  · exact h.1
  · have hxdet :
        LinearEquiv.det (lipschitzLinearRepresentation (Q := Q) x) = 1 := by
      rw [hx]
      simp
    have hodd : (-1 : Kˣ) ^ (Module.finrank K V - 1) = 1 := by
      rw [← h.2, hxdet]
    exact False.elim (hdet hodd)

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

/-- Every ambient spin-isometry value lies in the determinant-one subgroup. -/
theorem spinIsometryRepresentation_mem_specialOrthogonalGroup (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x ∈ Q.specialOrthogonalGroup := by
  change LinearEquiv.det
    (((spinIsometryRepresentation (Q := Q) x : Q.IsometryEquiv Q) : V ≃ₗ[K] V)) = 1
  simpa [spinIsometryRepresentation_toLinearEquiv] using
    spinLinearRepresentation_det_eq_one (Q := Q) x

/-- The full-orthogonal target image is contained in the determinant-one subgroup. -/
theorem spinIsometryRepresentation_range_le_specialOrthogonalGroup :
    MonoidHom.range (spinIsometryRepresentation (Q := Q)) ≤ Q.specialOrthogonalGroup := by
  rintro _ ⟨x, rfl⟩
  exact spinIsometryRepresentation_mem_specialOrthogonalGroup (Q := Q) x

/-- The ambient full-orthogonal image is exactly the image of the special-orthogonal spin map
after applying the subgroup inclusion. -/
theorem spinIsometryRepresentation_range_eq_map_specialOrthogonalRepresentationFiniteDimensional :
    MonoidHom.range (spinIsometryRepresentation (Q := Q)) =
      Subgroup.map (Q.specialOrthogonalGroup.subtype)
        (MonoidHom.range (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q))) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q) x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨gso, ⟨x, hx⟩, hg⟩
    refine ⟨x, ?_⟩
    rw [← hg, ← hx]
    rfl

/-- The ambient spin map cannot be surjective onto the full orthogonal group once the
orthogonal group contains an isometry of determinant different from `1`. Thus the special
orthogonal target is not just a convenience: it is forced by the determinant-one theorem for
spin actions. -/
theorem spinIsometryRepresentation_not_surjective_of_exists_det_ne_one
    (h : ∃ g : Q.IsometryEquiv Q, LinearEquiv.det (g : V ≃ₗ[K] V) ≠ 1) :
    ¬ Function.Surjective (spinIsometryRepresentation (Q := Q)) := by
  intro hsurj
  rcases h with ⟨g, hg⟩
  rcases hsurj g with ⟨x, hx⟩
  have hdetImage :
      LinearEquiv.det
          ((spinIsometryRepresentation (Q := Q) x : Q.IsometryEquiv Q) : V ≃ₗ[K] V) = 1 := by
    simpa [spinIsometryRepresentation_toLinearEquiv] using
      spinLinearRepresentation_det_eq_one (Q := Q) x
  exact hg (by simpa [hx] using hdetImage)

/-- Unit-valued determinant of the full isometry attached to a norm-`-1` pin generator. -/
theorem pinIsometryRepresentation_det_of_quadratic_eq_neg_one
    (a : V) (hq : Q a = -1) :
    LinearEquiv.det
        ((pinIsometryRepresentation (Q := Q)
            (pinIotaOfQuadraticEqNegOne (Q := Q) a hq) : Q.IsometryEquiv Q) : V ≃ₗ[K] V) =
      (-1 : Kˣ) ^ (Module.finrank K V - 1) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, pinIsometryRepresentation_toLinearEquiv]
  have ha : a ≠ 0 := by
    intro hzeroVec
    have hneg : (-1 : K) ≠ 0 := by simp
    apply hneg
    simpa [hzeroVec] using hq.symm
  have hfin : Module.finrank K (V ⧸ (K ∙ a)) = Module.finrank K V - 1 := by
    have hdim : Module.finrank K (V ⧸ (K ∙ a)) + 1 = Module.finrank K V := by
      simpa [finrank_span_singleton ha] using
        (K ∙ a : Submodule K V).finrank_quotient_add_finrank
    exact Nat.eq_sub_of_add_eq hdim
  simpa [pinIotaOfQuadraticEqNegOne, hfin] using
    pinLinearRepresentation_det_of_quadratic_eq_neg_one (Q := Q) a hq

/-- A norm-`-1` vector gives a concrete full-orthogonal obstruction to spin-map surjectivity
whenever the corresponding pin-generator determinant branch is not `1`. -/
theorem spinIsometryRepresentation_not_surjective_of_exists_quadratic_eq_neg_one_of_det_ne
    (hQ : ∃ a : V, Q a = -1)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1) :
    ¬ Function.Surjective (spinIsometryRepresentation (Q := Q)) := by
  rcases hQ with ⟨a, hqa⟩
  refine spinIsometryRepresentation_not_surjective_of_exists_det_ne_one (Q := Q) ?_
  refine ⟨pinIsometryRepresentation (Q := Q) (pinIotaOfQuadraticEqNegOne (Q := Q) a hqa), ?_⟩
  intro hg
  exact hdet
    ((pinIsometryRepresentation_det_of_quadratic_eq_neg_one (Q := Q) a hqa).symm.trans
      (by simpa [pinIsometryRepresentation_apply] using hg))

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

/-- A packaged pair-reflection lift in the special orthogonal target. These generators feed the
conditional covering theorem; the split-line results below show that unrestricted generation can
fail over fields with nonsquare units. -/
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
/-- The split special-orthogonal transport acts by the inverse dual map on the dual coordinate and
by the original linear automorphism on the primal coordinate. -/
@[simp]
theorem dualProdSpecialOrthogonalOfLinearEquiv_apply (e : W ≃ₗ[K] W)
    (d : Module.Dual K W) (u : W) :
    (dualProdSpecialOrthogonalOfLinearEquiv (K := K) e).1 (d, u) =
      (e.dualMap.symm d, e u) := rfl

omit [Invertible (2 : K)] in
/-- The linear automorphism that scales the distinguished line `K ∙ w` by `t` and fixes
`ker f`, under the normalization `f w = 1`. -/
def lineScalingLinearEquiv (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ) :
    W ≃ₗ[K] W where
  toFun u := u + ((((t : K) - 1) * f u) : K) • w
  invFun u := u + ((((t : K)⁻¹ - 1) * f u) : K) • w
  map_add' u v := by
    simp [mul_add, add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' c u := by
    simp [mul_assoc, smul_add, smul_smul, mul_left_comm, mul_comm]
  left_inv u := by
    have hfu :
        f (u + ((((t : K) - 1) * f u) : K) • w) = (t : K) * f u := by
      rw [map_add, map_smul]
      simp [hf]
      ring
    change
      u + ((((t : K) - 1) * f u) : K) • w +
          ((((t : K)⁻¹ - 1) * f (u + ((((t : K) - 1) * f u) : K) • w)) : K) • w = u
    rw [hfu, add_assoc, ← add_smul]
    have hcoef : (((t : K) - 1) * f u) + (((t : K)⁻¹ - 1) * ((t : K) * f u)) = 0 := by
      field_simp [t.ne_zero]
      ring
    rw [hcoef, zero_smul, add_zero]
  right_inv u := by
    have hfu :
        f (u + ((((t : K)⁻¹ - 1) * f u) : K) • w) = ((t : K)⁻¹) * f u := by
      rw [map_add, map_smul]
      simp [hf]
      ring
    change
      u + ((((t : K)⁻¹ - 1) * f u) : K) • w +
          ((((t : K) - 1) * f (u + ((((t : K)⁻¹ - 1) * f u) : K) • w)) : K) • w = u
    rw [hfu, add_assoc, ← add_smul]
    have hcoef : (((t : K)⁻¹ - 1) * f u) + (((t : K) - 1) * (((t : K)⁻¹) * f u)) = 0 := by
      field_simp [t.ne_zero]
      ring
    rw [hcoef, zero_smul, add_zero]

omit [Invertible (2 : K)] in
@[simp]
theorem lineScalingLinearEquiv_apply (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (u : W) :
    lineScalingLinearEquiv (f := f) (w := w) hf t u =
      u + ((((t : K) - 1) * f u) : K) • w := rfl

omit [Invertible (2 : K)] in
@[simp]
theorem lineScalingLinearEquiv_symm_apply (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (u : W) :
    (lineScalingLinearEquiv (f := f) (w := w) hf t).symm u =
      u + ((((t : K)⁻¹ - 1) * f u) : K) • w := rfl

omit [Invertible (2 : K)] in
/-- Transporting the line-scaling automorphism to the split special orthogonal group rescales the
primal line `K ∙ w` by `t` and the dual line `K ∙ f` by `t⁻¹`, fixing the complementary kernels. -/
@[simp]
theorem dualProdSpecialOrthogonalOfLinearEquiv_apply_lineScalingLinearEquiv
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (d : Module.Dual K W) (u : W) :
    (dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf t)).1 (d, u) =
      (d + ((((t : K)⁻¹ - 1) * d w) : K) • f,
        u + ((((t : K) - 1) * f u) : K) • w) := by
  rw [coe_dualProdSpecialOrthogonalOfLinearEquiv]
  change
      (((lineScalingLinearEquiv (f := f) (w := w) hf t).dualMap.symm d),
        lineScalingLinearEquiv (f := f) (w := w) hf t u) =
      (d + ((((t : K)⁻¹ - 1) * d w) : K) • f,
        u + ((((t : K) - 1) * f u) : K) • w)
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    rw [show ((lineScalingLinearEquiv (f := f) (w := w) hf t).dualMap.symm d) x =
        d ((lineScalingLinearEquiv (f := f) (w := w) hf t).symm x) by rfl]
    rw [lineScalingLinearEquiv_symm_apply]
    simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  · rfl

omit [Invertible (2 : K)] in
/-- The determinant-one transport of `GL(W)` into `SO(W* × W)` is multiplicative. -/
noncomputable def dualProdSpecialOrthogonalOfLinearEquivHom :
    (W ≃ₗ[K] W) →* (QuadraticForm.dualProd K W).specialOrthogonalGroup where
  toFun e := dualProdSpecialOrthogonalOfLinearEquiv (K := K) e
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' e f := by
    apply Subtype.ext
    rfl

omit [Invertible (2 : K)] in
@[simp]
theorem dualProdSpecialOrthogonalOfLinearEquivHom_apply (e : W ≃ₗ[K] W) :
    dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W) e =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K) e := rfl

omit [Invertible (2 : K)] in
/-- The split special-orthogonal transport remembers the underlying linear automorphism of `W`. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_injective :
    Function.Injective (dualProdSpecialOrthogonalOfLinearEquiv (K := K) (W := W)) := by
  intro e f h
  ext u
  have h' := congrArg
    (fun g : (QuadraticForm.dualProd K W).specialOrthogonalGroup =>
      Prod.snd (g.1 (0, u))) h
  simpa [dualProdSpecialOrthogonalOfLinearEquiv_apply] using h'

omit [Invertible (2 : K)] in
theorem dualProdSpecialOrthogonalOfLinearEquivHom_injective :
    Function.Injective (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)) :=
  dualProdSpecialOrthogonalOfLinearEquiv_injective (K := K) (W := W)

omit [Invertible (2 : K)] in
/-- The canonical `GL(W)` copy inside the split special orthogonal group of `W* × W`. -/
noncomputable def dualProdLeviSubgroup :
    Subgroup ((QuadraticForm.dualProd K W).specialOrthogonalGroup) :=
  (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)).range

omit [Invertible (2 : K)] in
/-- The split Levi subgroup is canonically isomorphic to `GL(W)`. -/
noncomputable def dualProdLeviSubgroupEquivLinearEquiv :
    (W ≃ₗ[K] W) ≃* dualProdLeviSubgroup (K := K) (W := W) :=
  MonoidHom.ofInjective
    (f := dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))
    (dualProdSpecialOrthogonalOfLinearEquivHom_injective (K := K) (W := W))

omit [Invertible (2 : K)] in
@[simp]
theorem dualProdLeviSubgroupEquivLinearEquiv_apply (e : W ≃ₗ[K] W) :
    dualProdLeviSubgroupEquivLinearEquiv (K := K) (W := W) e =
      ⟨dualProdSpecialOrthogonalOfLinearEquiv (K := K) e, ⟨e, rfl⟩⟩ := by
  apply Subtype.ext
  simpa [dualProdLeviSubgroup, dualProdLeviSubgroupEquivLinearEquiv] using
    (MonoidHom.ofInjective_apply
      (f := dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))
      (hf := dualProdSpecialOrthogonalOfLinearEquivHom_injective (K := K) (W := W))
      (x := e))

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

/-- The explicit Clifford-algebra unit whose conjugation acts as the transported hyperbolic
transvection attached to `(δ,w)` when `δ w = 0`. This is the unipotent candidate for lifting
Levi transvections into the spin image. -/
noncomputable def dualProdTransvectionCliffordUnit
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ where
  val := 1 + CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w)
  inv := 1 - CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w)
  val_inv := by
    let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
    let a : Module.Dual K W × W := (δ, 0)
    let b : Module.Dual K W × W := (0, w)
    let n : CliffordAlgebra Qd := CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b
    have hbab : CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b = 0 := by
      rw [CliffordAlgebra.ι_mul_ι_mul_ι]
      rw [show QuadraticMap.polar Qd b a = δ w by simp [QuadraticMap.polar, Qd, a, b]]
      rw [hδ]
      simp [Qd, a, b]
    have hnil : n * n = 0 := by
      calc
        n * n = CliffordAlgebra.ι Qd a *
            (CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b) := by
              dsimp [n]
              simp [mul_assoc]
        _ = 0 := by rw [hbab]; simp
    have hnil_assoc :
        CliffordAlgebra.ι Qd a *
            (CliffordAlgebra.ι Qd b * (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b)) = 0 := by
      simpa [n, mul_assoc] using hnil
    simpa [n, sub_eq_add_neg, add_mul, mul_add, mul_assoc, hnil_assoc,
      add_assoc, add_left_comm, add_comm]
  inv_val := by
    let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
    let a : Module.Dual K W × W := (δ, 0)
    let b : Module.Dual K W × W := (0, w)
    let n : CliffordAlgebra Qd := CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b
    have hbab : CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b = 0 := by
      rw [CliffordAlgebra.ι_mul_ι_mul_ι]
      rw [show QuadraticMap.polar Qd b a = δ w by simp [QuadraticMap.polar, Qd, a, b]]
      rw [hδ]
      simp [Qd, a, b]
    have hnil : n * n = 0 := by
      calc
        n * n = CliffordAlgebra.ι Qd a *
            (CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b) := by
              dsimp [n]
              simp [mul_assoc]
        _ = 0 := by rw [hbab]; simp
    have hnil_assoc :
        CliffordAlgebra.ι Qd a *
            (CliffordAlgebra.ι Qd b * (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b)) = 0 := by
      simpa [n, mul_assoc] using hnil
    simpa [n, sub_eq_add_neg, add_mul, mul_add, mul_assoc, hnil_assoc,
      add_assoc, add_left_comm, add_comm]

omit [Invertible (2 : K)] in
@[simp]
theorem coe_dualProdTransvectionCliffordUnit
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    ((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      1 + CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w) := rfl

omit [Invertible (2 : K)] in
@[simp]
theorem coe_inv_dualProdTransvectionCliffordUnit
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ)⁻¹ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      1 - CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w) := rfl

omit [Invertible (2 : K)] in
@[simp]
theorem dualProdTransvectionCliffordUnit_inv_eq
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ)⁻¹ =
      dualProdTransvectionCliffordUnit (K := K) (W := W) (-δ) w (by simpa using hδ) := by
  ext
  change 1 -
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w) =
    1 + CliffordAlgebra.ι (QuadraticForm.dualProd K W) (-δ, 0) *
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w)
  have hneg :
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (-δ, 0) *
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w) =
        -(CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w)) := by
    have hpair : ((-δ, 0) : Module.Dual K W × W) = -(δ, 0) := by
      ext <;> simp
    rw [hpair, map_neg]
    simp [neg_mul]
  rw [hneg]
  simp [sub_eq_add_neg]

omit [Invertible (2 : K)] in
@[simp]
theorem star_coe_dualProdTransvectionCliffordUnit
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    star (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) =
      (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ)⁻¹ :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let a : Module.Dual K W × W := (δ, 0)
  let b : Module.Dual K W × W := (0, w)
  rw [coe_dualProdTransvectionCliffordUnit, coe_inv_dualProdTransvectionCliffordUnit]
  change star (1 + CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b) =
      1 - CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b
  simp [CliffordAlgebra.star_ι]
  rw [CliffordAlgebra.ι_mul_ι_comm (Q := Qd) b a]
  rw [show QuadraticMap.polar Qd b a = δ w by simp [QuadraticMap.polar, Qd, a, b]]
  rw [hδ]
  simpa [sub_eq_add_neg]

omit [Invertible (2 : K)] in
/-- The explicit transvection unit is unitary: its Clifford star is its inverse. -/
theorem dualProdTransvectionCliffordUnit_mem_unitary
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) := by
  let x : CliffordAlgebra (QuadraticForm.dualProd K W) :=
    ((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))
  have hx : IsUnit x := (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ).isUnit
  rw [hx.mem_unitary_iff_star_mul_self]
  rw [show x =
      (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W))) by rfl]
  rw [star_coe_dualProdTransvectionCliffordUnit]
  simpa using
    (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ).inv_val

omit [Invertible (2 : K)] in
/-- The explicit transvection unit lies in the even Clifford subalgebra. -/
theorem dualProdTransvectionCliffordUnit_mem_even
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        CliffordAlgebra.even (QuadraticForm.dualProd K W) := by
  refine (CliffordAlgebra.even (QuadraticForm.dualProd K W)).add_mem ?_ ?_
  · exact (CliffordAlgebra.even (QuadraticForm.dualProd K W)).one_mem
  · change CliffordAlgebra.ι (QuadraticForm.dualProd K W) (δ, 0) *
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, w) ∈
          Subalgebra.toSubmodule (CliffordAlgebra.even (QuadraticForm.dualProd K W))
    simpa [CliffordAlgebra.even_toSubmodule] using
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
        (QuadraticForm.dualProd K W) (δ, 0) (0, w))

omit [Invertible (2 : K)] in
/-- Conjugation by the explicit unipotent Clifford unit `1 + ι(δ,0)ι(0,w)` realizes the transported
hyperbolic transvection on vectors. Later theorems package spin-group membership under the
orthogonal-normalization hypotheses needed for the finite-basis Levi image results. -/
theorem dualProdTransvectionCliffordUnit_conjAct_ι
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (d : Module.Dual K W) (u : W) :
    ConjAct.toConjAct
        (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ) •
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (d, u) =
      CliffordAlgebra.ι (QuadraticForm.dualProd K W) (d + (d w : K) • δ, u - (δ u : K) • w) := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let a : Module.Dual K W × W := (δ, 0)
  let b : Module.Dual K W × W := (0, w)
  let z : Module.Dual K W × W := (d, u)
  let n : CliffordAlgebra Qd := CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b
  have hn_left :
      n * CliffordAlgebra.ι Qd z =
        (d w : K) • CliffordAlgebra.ι Qd a -
          CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b := by
    dsimp [n]
    calc
      CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd z =
          CliffordAlgebra.ι Qd a *
            (algebraMap K (CliffordAlgebra Qd) (d w) -
              CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b) := by
                rw [mul_assoc, CliffordAlgebra.ι_mul_ι_comm (Q := Qd) b z]
                rw [show QuadraticMap.polar Qd b z = d w by
                  simp [QuadraticMap.polar, Qd, b, z]]
      _ = (d w : K) • CliffordAlgebra.ι Qd a -
          CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b := by
            rw [mul_sub]
            rw [show
              CliffordAlgebra.ι Qd a * algebraMap K (CliffordAlgebra Qd) (d w) =
                algebraMap K (CliffordAlgebra Qd) (d w) * CliffordAlgebra.ι Qd a by
                  exact (Algebra.commutes (A := CliffordAlgebra Qd) (d w)
                    (CliffordAlgebra.ι Qd a)).symm]
            rw [← Algebra.smul_def, mul_assoc]
  have hn_right :
      CliffordAlgebra.ι Qd z * n =
        (δ u : K) • CliffordAlgebra.ι Qd b -
          CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b := by
    dsimp [n]
    calc
      CliffordAlgebra.ι Qd z * (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b) =
          (algebraMap K (CliffordAlgebra Qd) (δ u) -
            CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z) * CliffordAlgebra.ι Qd b := by
              rw [← mul_assoc, CliffordAlgebra.ι_mul_ι_comm (Q := Qd) z a]
              rw [show QuadraticMap.polar Qd z a = δ u by
                simp [QuadraticMap.polar, Qd, z, a]]
      _ = (δ u : K) • CliffordAlgebra.ι Qd b -
          CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b := by
            rw [sub_mul, ← Algebra.smul_def, mul_assoc]
  have hnzn : n * CliffordAlgebra.ι Qd z * n = 0 := by
    have hleft :
        ((d w : K) • CliffordAlgebra.ι Qd a) * n = 0 := by
      calc
        ((d w : K) • CliffordAlgebra.ι Qd a) * n =
            (d w : K) • ((CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd a) *
              CliffordAlgebra.ι Qd b) := by
                dsimp [n]
                rw [smul_mul_assoc, mul_assoc]
        _ = 0 := by
          rw [CliffordAlgebra.ι_sq_scalar]
          simp [Qd, a]
    have hright :
        (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b) * n = 0 := by
      calc
        (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b) * n =
            CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z *
              (CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd b) := by
                dsimp [n]
                simp [mul_assoc]
        _ = 0 := by
          rw [CliffordAlgebra.ι_mul_ι_mul_ι]
          rw [show QuadraticMap.polar Qd b a = δ w by simp [QuadraticMap.polar, Qd, a, b]]
          rw [hδ]
          simp [Qd, a, b]
    rw [hn_left, sub_mul, hleft, hright]
    simp
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  change (1 + n) * CliffordAlgebra.ι Qd z * (1 - n) =
    CliffordAlgebra.ι Qd (d + (d w : K) • δ, u - (δ u : K) • w)
  have hexpand :
      (1 + n) * CliffordAlgebra.ι Qd z * (1 - n) =
        CliffordAlgebra.ι Qd z + (n * CliffordAlgebra.ι Qd z - CliffordAlgebra.ι Qd z * n) -
          n * CliffordAlgebra.ι Qd z * n := by
    calc
      (1 + n) * CliffordAlgebra.ι Qd z * (1 - n) =
          ((1 + n) * CliffordAlgebra.ι Qd z) * (1 - n) := by
            rw [mul_assoc]
      _ = (CliffordAlgebra.ι Qd z + n * CliffordAlgebra.ι Qd z) * (1 - n) := by
            rw [add_mul, one_mul]
      _ = (CliffordAlgebra.ι Qd z + n * CliffordAlgebra.ι Qd z) * 1 -
          (CliffordAlgebra.ι Qd z + n * CliffordAlgebra.ι Qd z) * n := by
            rw [mul_sub]
      _ = CliffordAlgebra.ι Qd z + n * CliffordAlgebra.ι Qd z -
          (CliffordAlgebra.ι Qd z * n + n * CliffordAlgebra.ι Qd z * n) := by
            rw [mul_one, add_mul, mul_assoc]
      _ = CliffordAlgebra.ι Qd z + (n * CliffordAlgebra.ι Qd z - CliffordAlgebra.ι Qd z * n) -
          n * CliffordAlgebra.ι Qd z * n := by
            abel
  have hcomm :
      n * CliffordAlgebra.ι Qd z - CliffordAlgebra.ι Qd z * n =
        (d w : K) • CliffordAlgebra.ι Qd a - (δ u : K) • CliffordAlgebra.ι Qd b := by
    rw [hn_left, hn_right]
    simpa using sub_sub_sub_cancel_right
      ((d w : K) • CliffordAlgebra.ι Qd a)
      ((δ u : K) • CliffordAlgebra.ι Qd b)
      (CliffordAlgebra.ι Qd a * CliffordAlgebra.ι Qd z * CliffordAlgebra.ι Qd b)
  calc
    (1 + n) * CliffordAlgebra.ι Qd z * (1 - n) =
        CliffordAlgebra.ι Qd z + (n * CliffordAlgebra.ι Qd z - CliffordAlgebra.ι Qd z * n) -
          n * CliffordAlgebra.ι Qd z * n := hexpand
    _ = CliffordAlgebra.ι Qd z + ((d w : K) • CliffordAlgebra.ι Qd a - (δ u : K) • CliffordAlgebra.ι Qd b) := by
      rw [hcomm, hnzn]
      simp
    _ = CliffordAlgebra.ι Qd (d + (d w : K) • δ, u - (δ u : K) • w) := by
      have hzsum : z + (d w : K) • a - (δ u : K) • b = (d + (d w : K) • δ, u - (δ u : K) • w) := by
        ext <;> simp [a, b, z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [← hzsum]
      rw [map_sub, map_add, map_smul, map_smul]
      rw [sub_eq_add_neg]
      conv_rhs => rw [sub_eq_add_neg]
      simpa [add_assoc]

omit [Invertible (2 : K)] in
/-- The explicit unipotent Clifford unit acts on vectors by the transported hyperbolic
transvection coming from `LinearEquiv.transvection (f := -δ) (v := w)`. -/
theorem dualProdTransvectionCliffordUnit_conjAct_eq_transvection
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (d : Module.Dual K W) (u : W) :
    ConjAct.toConjAct
        (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ) •
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (d, u) =
      CliffordAlgebra.ι (QuadraticForm.dualProd K W)
        (((dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ))).1) (d, u)) := by
  rw [dualProdTransvectionCliffordUnit_conjAct_ι,
    dualProdSpecialOrthogonalOfLinearEquiv_apply_transvection (K := K) (W := W)
      (δ := δ) (w := w) hδ]

omit [Invertible (2 : K)] in
/-- In particular, the explicit transvection unit sends each Clifford vector back into the vector
copy `ι(Q)(W* × W)`. -/
theorem dualProdTransvectionCliffordUnit_conjAct_ι_mem_range_ι
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (d : Module.Dual K W) (u : W) :
    ConjAct.toConjAct
        (dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ) •
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (d, u) ∈
        LinearMap.range (CliffordAlgebra.ι (QuadraticForm.dualProd K W)) := by
  rw [dualProdTransvectionCliffordUnit_conjAct_ι]
  exact LinearMap.mem_range_self _ _

omit [Invertible (2 : K)] in
/-- On a fixed split line, the explicit Clifford lifts of hyperbolic transvections multiply by adding
their dual parameters. -/
theorem dualProdTransvectionCliffordUnit_mul
    (δ η : Module.Dual K W) (w : W) (hδ : δ w = 0) (hη : η w = 0) :
    dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ *
        dualProdTransvectionCliffordUnit (K := K) (W := W) η w hη =
      dualProdTransvectionCliffordUnit (K := K) (W := W) (δ + η) w (by simpa [hδ, hη]) := by
  ext
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let aδ : Module.Dual K W × W := (δ, 0)
  let aη : Module.Dual K W × W := (η, 0)
  let b : Module.Dual K W × W := (0, w)
  have hb_sq : CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd b = 0 := by
    rw [CliffordAlgebra.ι_sq_scalar]
    simp [Qd, b]
  have hcross :
      (CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd b) *
          (CliffordAlgebra.ι Qd aη * CliffordAlgebra.ι Qd b) = 0 := by
    calc
      (CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd b) *
          (CliffordAlgebra.ι Qd aη * CliffordAlgebra.ι Qd b) =
          CliffordAlgebra.ι Qd aδ *
            ((CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd aη) *
              CliffordAlgebra.ι Qd b) := by
                simp [mul_assoc]
      _ = CliffordAlgebra.ι Qd aδ *
            ((-CliffordAlgebra.ι Qd aη * CliffordAlgebra.ι Qd b) *
              CliffordAlgebra.ι Qd b) := by
                rw [CliffordAlgebra.ι_mul_ι_comm (Q := Qd) b aη]
                rw [show QuadraticMap.polar Qd b aη = η w by
                  simp [QuadraticMap.polar, Qd, b, aη]]
                rw [hη]
                simp
      _ = -(CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd aη) *
            (CliffordAlgebra.ι Qd b * CliffordAlgebra.ι Qd b) := by
              simp [mul_assoc]
      _ = 0 := by rw [hb_sq]; simp
  change
      (1 + CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd b) *
          (1 + CliffordAlgebra.ι Qd aη * CliffordAlgebra.ι Qd b) =
        1 + CliffordAlgebra.ι Qd ((δ + η), 0) * CliffordAlgebra.ι Qd b
  simp [add_mul, mul_add, hcross, mul_assoc, add_assoc, add_left_comm, add_comm]
  have hsum :
      CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd b +
          CliffordAlgebra.ι Qd aη * CliffordAlgebra.ι Qd b =
        CliffordAlgebra.ι Qd ((δ + η), 0) * CliffordAlgebra.ι Qd b := by
    rw [← add_mul]
    have hpair : aδ + aη = ((δ + η), 0) := by
      ext <;> simp [aδ, aη]
    rw [← hpair, map_add]
  exact hsum

omit [Invertible (2 : K)] in
/-- Transvections along a fixed split line form an additive subgroup on their dual parameters. -/
theorem transvection_mul_transvection_eq_transvection_add
    (δ η : Module.Dual K W) (w : W) (hδ : δ w = 0) (hη : η w = 0) :
    LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ) *
        LinearEquiv.transvection (f := -η) (v := w) (by simpa using hη) =
      LinearEquiv.transvection (f := -(δ + η)) (v := w) (by simpa [hδ, hη]) := by
  ext u
  simp [LinearMap.transvection.apply, hδ, hη, sub_eq_add_neg, add_smul,
    add_assoc, add_left_comm, add_comm]

omit [Invertible (2 : K)] in
/-- Conjugating a fixed-line transvection by a chosen line scaling rescales its dual parameter by
the same scalar. -/
theorem lineScalingLinearEquiv_mul_transvection_mul_symm_eq
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (δ : Module.Dual K W) (hδ : δ w = 0) :
    lineScalingLinearEquiv (f := f) (w := w) hf t *
        LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ) *
        (lineScalingLinearEquiv (f := f) (w := w) hf t).symm =
      LinearEquiv.transvection (f := -(((t : K) • δ))) (v := w)
        (by simpa [smul_eq_mul] using hδ) := by
  ext u
  let e := lineScalingLinearEquiv (f := f) (w := w) hf t
  change e ((LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) (e.symm u)) =
    LinearEquiv.transvection (f := -(((t : K) • δ))) (v := w)
      (by simpa [smul_eq_mul] using hδ) u
  have hδe : δ (e.symm u) = δ u := by
    rw [lineScalingLinearEquiv_symm_apply]
    simp [hδ]
  have hew : e w = (t : K) • w := by
    rw [lineScalingLinearEquiv_apply]
    calc
      w + ((((t : K) - 1) * f w) : K) • w = w + (((t : K) - 1) : K) • w := by
        rw [hf, mul_one]
      _ = (((1 : K) + ((t : K) - 1)) : K) • w := by
        rw [add_smul, one_smul]
      _ = (t : K) • w := by simp
  calc
    e ((LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) (e.symm u)) =
      e (e.symm u - (δ (e.symm u) : K) • w) := by
        simp [LinearMap.transvection.apply, sub_eq_add_neg]
    _ = e (e.symm u) - (δ (e.symm u) : K) • e w := by
        simp [map_sub, map_smul]
    _ = u - (δ u : K) • ((t : K) • w) := by rw [e.apply_symm_apply, hδe, hew]
    _ = u - (((t : K) * δ u) : K) • w := by
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = LinearEquiv.transvection (f := -(((t : K) • δ))) (v := w)
          (by simpa [smul_eq_mul] using hδ) u := by
        simp [LinearMap.transvection.apply, sub_eq_add_neg, smul_eq_mul, mul_assoc, mul_comm]

omit [Invertible (2 : K)] in
/-- Transporting the fixed-line transvection subgroup to `SO(W* × W)` preserves its additive law. -/
theorem dualProdSpecialOrthogonalOf_transvection_mul_transvection_eq_transvection_add
    (δ η : Module.Dual K W) (w : W) (hδ : δ w = 0) (hη : η w = 0) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -η) (v := w) (by simpa using hη)) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(δ + η)) (v := w) (by simpa [hδ, hη])) := by
  have h :=
    congrArg (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))
      (transvection_mul_transvection_eq_transvection_add (K := K) (W := W)
        (δ := δ) (η := η) (w := w) hδ hη)
  simpa [dualProdSpecialOrthogonalOfLinearEquivHom_apply, map_mul] using h

omit [Invertible (2 : K)] in
/-- The chosen line-scaling torus acts on the transported fixed-line transvection subgroup with the
expected weight-one action on `W`, hence weight-two on the induced square torus in `SO(W* × W)`. -/
theorem dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_mul_transvection_mul_inv_eq
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (δ : Module.Dual K W) (hδ : δ w = 0) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf t) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) *
      (dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf t))⁻¹ =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(((t : K) • δ))) (v := w)
          (by simpa [smul_eq_mul] using hδ)) := by
  have h :=
    congrArg (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))
      (lineScalingLinearEquiv_mul_transvection_mul_symm_eq (K := K) (W := W)
        (f := f) (w := w) hf (t := t) (δ := δ) hδ)
  simpa [dualProdSpecialOrthogonalOfLinearEquivHom_apply, map_mul, map_inv] using h

omit [Invertible (2 : K)] in
/-- Two complementary line scalings with inverse parameters factor as four linear transvections.
This is the basis-free two-line diagonal block identity used later in determinant-one Levi
factorizations. -/
theorem complementaryLineScalings_eq_transvection_four
    (f g : Module.Dual K W) (w u : W)
    (hf : f w = 1) (hg : g u = 1) (hfu : f u = 0) (hgw : g w = 0)
    (a : Kˣ) :
    lineScalingLinearEquiv (f := f) (w := w) hf a *
        lineScalingLinearEquiv (f := g) (w := u) hg a⁻¹ =
      LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)) • w))
        (by simp [hgw]) *
      LinearEquiv.transvection (f := -f) (v := ((-1 : K) • u))
        (by simp [hfu]) *
      LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)⁻¹) • w))
        (by simp [hgw]) *
      LinearEquiv.transvection (f := -f) (v := ((a : K) • u))
        (by simp [hfu]) := by
  ext x
  let eL : W ≃ₗ[K] W :=
    lineScalingLinearEquiv (f := f) (w := w) hf a *
      lineScalingLinearEquiv (f := g) (w := u) hg a⁻¹
  let t1 : W ≃ₗ[K] W :=
    LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)) • w))
      (by simp [hgw])
  let t2 : W ≃ₗ[K] W :=
    LinearEquiv.transvection (f := -f) (v := ((-1 : K) • u))
      (by simp [hfu])
  let t3 : W ≃ₗ[K] W :=
    LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)⁻¹) • w))
      (by simp [hgw])
  let t4 : W ≃ₗ[K] W :=
    LinearEquiv.transvection (f := -f) (v := ((a : K) • u))
      (by simp [hfu])
  let eR : W ≃ₗ[K] W := t1 * t2 * t3 * t4
  change eL x = eR x
  let z : W := x - (f x : K) • w - (g x : K) • u
  have hx : x = (f x : K) • w + (g x : K) • u + z := by
    dsimp [z]
    abel
  have hfz : f z = 0 := by
    dsimp [z]
    simp [hf, hfu]
  have hgz : g z = 0 := by
    dsimp [z]
    simp [hg, hgw]
  have hz_left : eL z = z := by
    dsimp [eL]
    simp [lineScalingLinearEquiv_apply, hfz, hgz]
  have hw_left : eL w = (a : K) • w := by
    dsimp [eL]
    simp [lineScalingLinearEquiv_apply, hf, hg, hfu, hgw, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
    calc
      w + (((a : K) - 1 : K) • w) = (((1 : K) + ((a : K) - 1)) : K) • w := by
        rw [add_smul, one_smul]
      _ = (a : K) • w := by
        congr 1
        ring
  have hu_left : eL u = ((a : K)⁻¹) • u := by
    dsimp [eL]
    simp [lineScalingLinearEquiv_apply, hf, hg, hfu, hgw, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
    calc
      u + ((((a : K)⁻¹) - 1 : K) • u) = (((1 : K) + (((a : K)⁻¹) - 1)) : K) • u := by
        rw [add_smul, one_smul]
      _ = ((a : K)⁻¹) • u := by
        congr 1
        ring
  have hz_right : eR z = z := by
    dsimp [eR, t1, t2, t3, t4]
    simp [LinearEquiv.mul_apply, LinearMap.transvection.apply, hfz, hgz, sub_eq_add_neg]
  have ht4w : t4 w = w - (a : K) • u := by
    dsimp [t4]
    simp [LinearMap.transvection.apply, hf, hfu, sub_eq_add_neg, smul_smul, mul_assoc, mul_comm]
  have ht3w : t3 (t4 w) = (a : K) • w - (a : K) • u := by
    rw [ht4w]
    dsimp [t3]
    have hg_t4w : g (w - (a : K) • u) = -(a : K) := by
      simp [hg, hgw]
    rw [LinearMap.transvection.apply, show (-g) (w - (a : K) • u) = (a : K) by simpa [hg_t4w]]
    have hwcoeff : w + (a : K) • ((((1 : K) - (a : K)⁻¹) : K) • w) = (a : K) • w := by
      rw [smul_smul]
      calc
        w + (((a : K) * (((1 : K) - (a : K)⁻¹) : K)) : K) • w =
            (((1 : K) + (a : K) * (((1 : K) - (a : K)⁻¹) : K)) : K) • w := by
              rw [add_smul, one_smul]
        _ = (a : K) • w := by
          field_simp [a.ne_zero]
          ring
    calc
      w - (a : K) • u + (a : K) • ((((1 : K) - (a : K)⁻¹) : K) • w) =
          (w + (a : K) • ((((1 : K) - (a : K)⁻¹) : K) • w)) - (a : K) • u := by
            abel
      _ = (a : K) • w - (a : K) • u := by rw [hwcoeff]
  have ht2w : t2 (t3 (t4 w)) = (a : K) • w := by
    rw [ht3w]
    dsimp [t2]
    have hf_t3w : f ((a : K) • w - (a : K) • u) = (a : K) := by
      simp [hf, hfu]
    rw [LinearMap.transvection.apply,
      show (-f) ((a : K) • w - (a : K) • u) = -(a : K) by simpa [hf_t3w]]
    simp [sub_eq_add_neg, smul_smul, mul_assoc, mul_comm, mul_left_comm]
  have hw_right : eR w = (a : K) • w := by
    dsimp [eR]
    rw [ht2w]
    dsimp [t1]
    simp [LinearMap.transvection.apply, hgw]
  have ht4u : t4 u = u := by
    dsimp [t4]
    simp [LinearMap.transvection.apply, hfu]
  have ht3u : t3 (t4 u) = u + ((((a : K)⁻¹) - 1 : K) • w) := by
    rw [ht4u]
    dsimp [t3]
    rw [LinearMap.transvection.apply]
    simp [hg, hgw, sub_eq_add_neg, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  have ht2u :
      t2 (t3 (t4 u)) = ((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w) := by
    rw [ht3u]
    dsimp [t2]
    have hf_t3u : f (u + ((((a : K)⁻¹) - 1 : K) • w) ) = ((a : K)⁻¹) - 1 := by
      simp [hf, hfu]
    rw [LinearMap.transvection.apply,
      show (-f) (u + ((((a : K)⁻¹) - 1 : K) • w)) = -(((a : K)⁻¹) - 1) by
        simpa [hf_t3u]]
    have hsmul :
        (-(((a : K)⁻¹) - 1) : K) • ((-1 : K) • u) = (((a : K)⁻¹) - 1 : K) • u := by
      rw [smul_smul]
      congr 1
      ring
    calc
      u + ((((a : K)⁻¹) - 1 : K) • w) + (-(((a : K)⁻¹) - 1) : K) • ((-1 : K) • u) =
          u + ((((a : K)⁻¹) - 1 : K) • w) + ((((a : K)⁻¹) - 1 : K) • u) := by
            rw [hsmul]
      _ = ((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w) := by
        calc
          u + ((((a : K)⁻¹) - 1 : K) • w) + ((((a : K)⁻¹) - 1 : K) • u) =
          u + ((((a : K)⁻¹) - 1 : K) • u) + ((((a : K)⁻¹) - 1 : K) • w) := by
                abel
          _ = ((((1 : K) + (((a : K)⁻¹) - 1)) : K) • u) +
                ((((a : K)⁻¹) - 1 : K) • w) := by
                  rw [add_smul, one_smul]
          _ = ((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w) := by
                congr 1
                ring
  have hu_right : eR u = ((a : K)⁻¹) • u := by
    dsimp [eR]
    rw [ht2u]
    dsimp [t1]
    have hg_t2u :
        g (((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w)) = (a : K)⁻¹ := by
      simp [hg, hgw]
    rw [LinearMap.transvection.apply,
      show (-g) (((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w)) = -((a : K)⁻¹) by
        simpa [hg_t2u]]
    calc
      ((a : K)⁻¹) • u + ((((a : K)⁻¹) - 1 : K) • w) +
          (-((a : K)⁻¹) : K) • ((((1 : K) - (a : K)) : K) • w) =
            ((a : K)⁻¹) • u +
              (((((a : K)⁻¹) - 1) + (-((a : K)⁻¹)) * (((1 : K) - (a : K)) : K)) : K) • w := by
                simpa [add_smul, smul_smul, add_assoc]
      _ = ((a : K)⁻¹) • u := by
        have hcoef :
            ((((a : K)⁻¹) - 1) + (-((a : K)⁻¹)) * (((1 : K) - (a : K)) : K) : K) = 0 := by
          field_simp [a.ne_zero]
          ring
        rw [hcoef, zero_smul, add_zero]
  have hleft :
      eL x = (((a : K) * f x) : K) • w + ((((a : K)⁻¹) * g x) : K) • u + z := by
    calc
      eL x = eL ((f x : K) • w + (g x : K) • u + z) := by
        conv_lhs => rw [hx]
      _ = (f x : K) • eL w + (g x : K) • eL u + eL z := by
        simp [map_add, map_smul]
      _ = (f x : K) • ((a : K) • w) + (g x : K) • (((a : K)⁻¹) • u) + z := by
        rw [hw_left, hu_left, hz_left]
      _ = (((a : K) * f x) : K) • w + ((((a : K)⁻¹) * g x) : K) • u + z := by
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
  have hright :
      eR x = (((a : K) * f x) : K) • w + ((((a : K)⁻¹) * g x) : K) • u + z := by
    calc
      eR x = eR ((f x : K) • w + (g x : K) • u + z) := by
        conv_lhs => rw [hx]
      _ = (f x : K) • eR w + (g x : K) • eR u + eR z := by
        simp [map_add, map_smul]
      _ = (f x : K) • ((a : K) • w) + (g x : K) • (((a : K)⁻¹) • u) + z := by
        rw [hw_right, hu_right, hz_right]
      _ = (((a : K) * f x) : K) • w + ((((a : K)⁻¹) * g x) : K) • u + z := by
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
  exact hleft.trans hright.symm

omit [Invertible (2 : K)] in
/-- Transporting the complementary two-line scaling identity to `SO(W* × W)` gives an explicit
four-transvection factorization in the orthogonal action. -/
theorem dualProdSpecialOrthogonalOf_complementaryLineScalings_eq_transvection_four
    (f g : Module.Dual K W) (w u : W)
    (hf : f w = 1) (hg : g u = 1) (hfu : f u = 0) (hgw : g w = 0)
    (a : Kˣ) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf a *
          lineScalingLinearEquiv (f := g) (w := u) hg a⁻¹) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)) • w))
          (by simp [hgw])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -f) (v := ((-1 : K) • u))
          (by simp [hfu])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -g) (v := (((1 : K) - (a : K)⁻¹) • w))
          (by simp [hgw])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -f) (v := ((a : K) • u))
          (by simp [hfu])) := by
  have h :=
    congrArg (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))
      (complementaryLineScalings_eq_transvection_four (K := K) (W := W)
        (f := f) (g := g) (w := w) (u := u) hf hg hfu hgw a)
  simpa [dualProdSpecialOrthogonalOfLinearEquivHom_apply, map_mul] using h

section BasisScaling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Invertible (2 : K)] in
/-- The basis transvection attached to a matrix transvection structure. It sends the distinguished
basis line `b t.j` to itself plus `t.c` times `b t.i`, fixing the remaining basis lines. -/
noncomputable def basisTransvectionLinearEquiv
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) : W ≃ₗ[K] W :=
  LinearEquiv.transvection (f := (t.c : K) • b.coord t.j) (v := b t.i) (by
    simp [Module.Basis.coord_apply, t.hij])

omit [Invertible (2 : K)] in
@[simp] theorem basisTransvectionLinearEquiv_toMatrix
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    LinearMap.toMatrix b b
        ((basisTransvectionLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W) =
      t.toMatrix := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
  by_cases hij : i = t.i
  · subst hij
    by_cases hjj : j = t.j
    · subst hjj
      simp [basisTransvectionLinearEquiv, LinearMap.transvection.apply, Module.Basis.coord_apply,
        t.hij]
    · by_cases hji : j = t.i
      · subst hji
        have hneq : t.j ≠ t.i := by
          intro h
          exact t.hij h.symm
        simpa [basisTransvectionLinearEquiv, LinearMap.transvection.apply,
          Module.Basis.coord_apply, Matrix.single_apply, Finsupp.single_apply, hneq, t.hij]
      · simpa [basisTransvectionLinearEquiv, LinearMap.transvection.apply,
          Module.Basis.coord_apply, Matrix.one_apply, Matrix.single_apply, Finsupp.single_apply,
          hjj, hji, eq_comm]
  · by_cases hjj : j = t.j
    · subst hjj
      simpa [basisTransvectionLinearEquiv, LinearMap.transvection.apply,
        Module.Basis.coord_apply, Matrix.one_apply, Matrix.single_apply, Finsupp.single_apply,
        hij, eq_comm]
    · simpa [basisTransvectionLinearEquiv, LinearMap.transvection.apply,
        Module.Basis.coord_apply, Matrix.one_apply, Matrix.single_apply, Finsupp.single_apply,
        hij, hjj, eq_comm]

omit [Invertible (2 : K)] in
@[simp] theorem dualProdSpecialOrthogonalOfLinearEquiv_apply_basisTransvectionLinearEquiv
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    (d : Module.Dual K W) (u : W) :
    (dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t)).1 (d, u) =
      (d - (d (b t.i) : K) • ((t.c : K) • b.coord t.j),
        u + (((t.c : K) • b.coord t.j) u : K) • b t.i) := by
  simpa [basisTransvectionLinearEquiv, sub_eq_add_neg] using
    (dualProdSpecialOrthogonalOfLinearEquiv_apply_transvection (K := K) (W := W)
      (δ := -((t.c : K) • b.coord t.j)) (w := b t.i) (by
        simp [Module.Basis.coord_apply, t.hij]) d u)

omit [Invertible (2 : K)] in
/-- The explicit Clifford unit candidate attached to a basis transvection. Its conjugation realizes
the transported basis transvection on `W* × W`. -/
noncomputable def basisTransvectionCliffordUnit
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ :=
  dualProdTransvectionCliffordUnit (K := K) (W := W) (-((t.c : K) • b.coord t.j)) (b t.i) (by
    simp [Module.Basis.coord_apply, t.hij])

omit [Invertible (2 : K)] in
@[simp] theorem coe_basisTransvectionCliffordUnit
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    ((basisTransvectionCliffordUnit (K := K) (W := W) b t :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      1 - CliffordAlgebra.ι (QuadraticForm.dualProd K W) (((t.c : K) • b.coord t.j), 0) *
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, b t.i) := by
  rw [basisTransvectionCliffordUnit, coe_dualProdTransvectionCliffordUnit]
  have hpair :
      ((-((t.c : K) • b.coord t.j), 0) : Module.Dual K W × W) =
        -((((t.c : K) • b.coord t.j), 0) : Module.Dual K W × W) := by
    ext <;> simp
  rw [hpair, map_neg]
  simp [sub_eq_add_neg, neg_mul]

omit [Invertible (2 : K)] in
theorem basisTransvectionCliffordUnit_mem_unitary
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    (((basisTransvectionCliffordUnit (K := K) (W := W) b t :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) := by
  simpa [basisTransvectionCliffordUnit] using
    (dualProdTransvectionCliffordUnit_mem_unitary (K := K) (W := W)
      (-((t.c : K) • b.coord t.j)) (b t.i) (by simp [Module.Basis.coord_apply, t.hij]))

omit [Invertible (2 : K)] in
theorem basisTransvectionCliffordUnit_mem_even
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    (((basisTransvectionCliffordUnit (K := K) (W := W) b t :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        CliffordAlgebra.even (QuadraticForm.dualProd K W) := by
  simpa [basisTransvectionCliffordUnit] using
    (dualProdTransvectionCliffordUnit_mem_even (K := K) (W := W)
      (-((t.c : K) • b.coord t.j)) (b t.i) (by simp [Module.Basis.coord_apply, t.hij]))

omit [Invertible (2 : K)] in
theorem basisTransvectionCliffordUnit_conjAct_eq_basisTransvectionLinearEquiv
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    (d : Module.Dual K W) (u : W) :
    ConjAct.toConjAct (basisTransvectionCliffordUnit (K := K) (W := W) b t) •
        CliffordAlgebra.ι (QuadraticForm.dualProd K W) (d, u) =
      CliffordAlgebra.ι (QuadraticForm.dualProd K W)
        (((dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisTransvectionLinearEquiv (K := K) (W := W) b t)).1) (d, u)) := by
  unfold basisTransvectionCliffordUnit
  simpa [basisTransvectionLinearEquiv] using
    (dualProdTransvectionCliffordUnit_conjAct_eq_transvection (K := K) (W := W)
      (-((t.c : K) • b.coord t.j)) (b t.i) (by simp [Module.Basis.coord_apply, t.hij]) d u)

/-- The linear equivalence that rescales each basis vector `b i` by the unit `t i`. -/
noncomputable def basisScalingLinearEquiv (b : Module.Basis ι K W) (t : ι → Kˣ) : W ≃ₗ[K] W :=
  ((b.equivFun).trans (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (t i))).trans
    b.equivFun.symm

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_apply_basis
    (b : Module.Basis ι K W) (t : ι → Kˣ) (i : ι) :
    basisScalingLinearEquiv (K := K) (W := W) b t (b i) = (t i : K) • b i := by
  classical
  change b.equivFun.symm
      ((LinearEquiv.piCongrRight fun j => LinearEquiv.smulOfUnit (t j)) (b.equivFun (b i))) =
    (t i : K) • b i
  rw [Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_eq_single i]
  · simpa [LinearEquiv.smulOfUnit, Units.smul_def]
  · intro j hj hji
    simp [Finsupp.single_apply, hji, LinearEquiv.smulOfUnit, Units.smul_def]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_toMatrix
    (b : Module.Basis ι K W) (t : ι → Kˣ) :
    LinearMap.toMatrix b b
        ((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W) =
      Matrix.diagonal fun i => (t i : K) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa [LinearMap.toMatrix_apply, Matrix.diagonal, Finsupp.single_apply, eq_comm] using
      congrArg (fun x => b.coord j x)
        (basisScalingLinearEquiv_apply_basis (K := K) (W := W) (b := b) (t := t) (i := j))
  · simpa [LinearMap.toMatrix_apply, Matrix.diagonal, Finsupp.single_apply, hij, eq_comm] using
      congrArg (fun x => b.coord i x)
        (basisScalingLinearEquiv_apply_basis (K := K) (W := W) (b := b) (t := t) (i := j))

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_det
    (b : Module.Basis ι K W) (t : ι → Kˣ) :
    LinearEquiv.det (basisScalingLinearEquiv (K := K) (W := W) b t) = ∏ i, t i := by
  apply Units.ext
  calc
    (LinearEquiv.det (basisScalingLinearEquiv (K := K) (W := W) b t) : K) =
        LinearMap.det
          ((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W) := by
          simp [LinearEquiv.coe_det]
    _ = Matrix.det
          (LinearMap.toMatrix b b
            ((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W)) := by
          rw [LinearMap.det_toMatrix]
    _ = Matrix.det (Matrix.diagonal fun i => (t i : K)) := by
          rw [basisScalingLinearEquiv_toMatrix]
    _ = ∏ i, (t i : K) := by
          rw [Matrix.det_diagonal]
    _ = ((∏ i, t i : Kˣ) : K) := by
          simp

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_det_update
    (b : Module.Basis ι K W) (i : ι) (a : Kˣ) :
    LinearEquiv.det
        (basisScalingLinearEquiv (K := K) (W := W) b (Function.update (1 : ι → Kˣ) i a)) =
      a := by
  rw [basisScalingLinearEquiv_det]
  apply Units.ext
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hji
    simp [Function.update, hji]

omit [Invertible (2 : K)] in
@[simp] theorem list_prod_basisTransvectionLinearEquiv_toMatrix
    (b : Module.Basis ι K W) (L : List (Matrix.TransvectionStruct ι K)) :
    LinearMap.toMatrix b b
        (((L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod : W ≃ₗ[K] W) :
          W →ₗ[K] W) =
      (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L IH =>
      simp [LinearMap.toMatrix_mul, IH]

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_one
    (b : Module.Basis ι K W) :
    basisScalingLinearEquiv (K := K) (W := W) b (1 : ι → Kˣ) = 1 := by
  apply b.ext'
  intro i
  rw [basisScalingLinearEquiv_apply_basis]
  simp

omit [Invertible (2 : K)] in
@[simp] theorem basisScalingLinearEquiv_mul
    (b : Module.Basis ι K W) (t s : ι → Kˣ) :
    basisScalingLinearEquiv (K := K) (W := W) b (t * s) =
      basisScalingLinearEquiv (K := K) (W := W) b t *
        basisScalingLinearEquiv (K := K) (W := W) b s := by
  apply b.ext'
  intro i
  rw [LinearEquiv.mul_apply, basisScalingLinearEquiv_apply_basis, basisScalingLinearEquiv_apply_basis]
  rw [map_smul, basisScalingLinearEquiv_apply_basis]
  simpa [Pi.mul_apply, smul_smul] using
    congrArg (fun c : K => c • b i) (mul_comm (t i : K) (s i : K))

omit [Invertible (2 : K)] in
theorem basisScalingLinearEquiv_update_eq_lineScalingLinearEquiv
    (b : Module.Basis ι K W) (i : ι) (a : Kˣ) :
    basisScalingLinearEquiv (K := K) (W := W) b (Function.update (1 : ι → Kˣ) i a) =
      lineScalingLinearEquiv (f := b.coord i) (w := b i)
        (by simp [Module.Basis.coord_apply]) a := by
  apply b.ext'
  intro k
  by_cases hki : k = i
  · subst hki
    rw [basisScalingLinearEquiv_apply_basis]
    simp [lineScalingLinearEquiv_apply, Module.Basis.coord_apply]
    symm
    calc
      b k + (((a : K) - 1 : K) • b k) = (((1 : K) + ((a : K) - 1)) : K) • b k := by
        rw [add_smul, one_smul]
      _ = (a : K) • b k := by
        congr 1
        ring
  · rw [basisScalingLinearEquiv_apply_basis]
    simp [lineScalingLinearEquiv_apply, Module.Basis.coord_apply, hki]

omit [Invertible (2 : K)] in
noncomputable def basisScalingLinearEquivHom
    (b : Module.Basis ι K W) :
    (ι → Kˣ) →* (W ≃ₗ[K] W) where
  toFun t := basisScalingLinearEquiv (K := K) (W := W) b t
  map_one' := basisScalingLinearEquiv_one (K := K) (W := W) b
  map_mul' t s := basisScalingLinearEquiv_mul (K := K) (W := W) b t s

omit [Invertible (2 : K)] in
/-- A basis-diagonal block with entries `a` and `a⁻¹` on complementary basis lines is exactly the
product of the corresponding two line scalings. -/
theorem basisScalingLinearEquiv_two_update
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    basisScalingLinearEquiv (K := K) (W := W) b
        (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹) =
      lineScalingLinearEquiv (f := b.coord i) (w := b i)
          (by simp [Module.Basis.coord_apply]) a *
        lineScalingLinearEquiv (f := b.coord j) (w := b j)
          (by simp [Module.Basis.coord_apply]) a⁻¹ := by
  apply b.ext'
  intro k
  by_cases hki : k = i
  · subst hki
    rw [basisScalingLinearEquiv_apply_basis]
    simp [lineScalingLinearEquiv_apply, Module.Basis.coord_apply, hij]
    symm
    calc
      b k + (((a : K) - 1 : K) • b k) = (((1 : K) + ((a : K) - 1)) : K) • b k := by
        rw [add_smul, one_smul]
      _ = (a : K) • b k := by
        congr 1
        ring
  · by_cases hkj : k = j
    · subst hkj
      rw [basisScalingLinearEquiv_apply_basis]
      simp [lineScalingLinearEquiv_apply, Module.Basis.coord_apply, hij, hki]
      symm
      calc
        b k + ((((a : K)⁻¹) - 1 : K) • b k) =
            (((1 : K) + (((a : K)⁻¹) - 1)) : K) • b k := by
              rw [add_smul, one_smul]
        _ = ((a : K)⁻¹) • b k := by
              congr 1
              ring
    · rw [basisScalingLinearEquiv_apply_basis]
      simp [lineScalingLinearEquiv_apply, Module.Basis.coord_apply, hij, hki, hkj]

omit [Invertible (2 : K)] in
theorem twoUpdateScaling_pairwise
    (i : ι) (t : ι → Kˣ) :
    (Finset.univ.erase i : Set ι).Pairwise fun j k =>
      Commute
        (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)
        (Function.update (Function.update (1 : ι → Kˣ) k (t k)) i (t k)⁻¹) := by
  intro j _ k _ _
  exact Commute.all _ _

omit [Invertible (2 : K)] in
theorem twoUpdateScaling_prod_eq_of_base
    (i : ι) (t : ι → Kˣ)
    (hbase : t i = (Finset.univ.erase i).prod fun j => (t j)⁻¹) :
    ((Finset.univ.erase i).prod fun j =>
        Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹) = t := by
  funext k
  apply Units.ext
  by_cases hki : k = i
  · subst k
    have hval :
        ((Finset.univ.erase i).prod fun j =>
            (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹) i) =
          (Finset.univ.erase i).prod fun j => (t j)⁻¹ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update, hji]
    simpa [hval] using congrArg (fun u : Kˣ => (u : K)) hbase.symm
  · have hk : k ∈ Finset.univ.erase i := by simp [hki]
    have hsingle :
        ((Finset.univ.erase i).prod fun j =>
          (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹) k) =
            (Function.update (Function.update (1 : ι → Kˣ) k (t k)) i (t k)⁻¹) k := by
      apply Finset.prod_eq_single_of_mem k hk
      intro j hj hjk
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [Function.update, hki, hji, hkj]
    simpa [hsingle, Function.update, hki]

omit [Invertible (2 : K)] in
theorem basisScalingLinearEquiv_two_update_pairwise
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) :
    (Finset.univ.erase i : Set ι).Pairwise fun j k =>
      Commute
        (basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
        (basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (1 : ι → Kˣ) k (t k)) i (t k)⁻¹)) := by
  intro j hj k hk hjk
  exact
    (Commute.all
      (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)
      (Function.update (Function.update (1 : ι → Kˣ) k (t k)) i (t k)⁻¹)).map
      (basisScalingLinearEquivHom (K := K) (W := W) b)

omit [Invertible (2 : K)] in
/-- If the scaling on a distinguished basis line equals the inverse product of the remaining basis
scalings, then the whole basis scaling factors as the noncommutative product of the corresponding
canonical `2×2` determinant-one blocks. -/
theorem basisScalingLinearEquiv_eq_noncommProd_two_update_of_base
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ)
    (hbase : t i = (Finset.univ.erase i).prod fun j => (t j)⁻¹) :
    basisScalingLinearEquiv (K := K) (W := W) b t =
      (Finset.univ.erase i).noncommProd
        (fun j =>
          basisScalingLinearEquiv (K := K) (W := W) b
            (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
        (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := t)) := by
  let u : ι → ι → Kˣ := fun j =>
    Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹
  have hprod : ((Finset.univ.erase i).prod u) = t := by
    simpa [u] using twoUpdateScaling_prod_eq_of_base (K := K) (i := i) (t := t) hbase
  have hcomm : (Finset.univ.erase i : Set ι).Pairwise fun j k => Commute (u j) (u k) := by
    simpa [u] using twoUpdateScaling_pairwise (K := K) (i := i) (t := t)
  calc
    basisScalingLinearEquiv (K := K) (W := W) b t =
        basisScalingLinearEquivHom (K := K) (W := W) b
          ((Finset.univ.erase i).noncommProd u hcomm) := by
            rw [Finset.noncommProd_eq_prod, hprod]
            rfl
    _ = (Finset.univ.erase i).noncommProd
          (fun j =>
            basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
          (basisScalingLinearEquiv_two_update_pairwise
            (K := K) (W := W) (b := b) (i := i) (t := t)) := by
              simpa [u] using
                (Finset.map_noncommProd (s := Finset.univ.erase i) (f := u) hcomm
                  (g := basisScalingLinearEquivHom (K := K) (W := W) b))

omit [Invertible (2 : K)] in
/-- Transporting the basis-diagonal factorization to `SO(W* × W)` factors the corresponding Levi
element into canonical determinant-one `2×2` blocks. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_noncommProd_two_update_of_base
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ)
    (hbase : t i = (Finset.univ.erase i).prod fun j => (t j)⁻¹) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) =
      (Finset.univ.erase i).noncommProd
        (fun j =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
        (by
          intro j hj k hk hjk
          exact
            (basisScalingLinearEquiv_two_update_pairwise
              (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
              (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))) := by
  rw [basisScalingLinearEquiv_eq_noncommProd_two_update_of_base
    (K := K) (W := W) (b := b) (i := i) (t := t) hbase]
  simpa [dualProdSpecialOrthogonalOfLinearEquivHom_apply] using
    (Finset.map_noncommProd (s := Finset.univ.erase i)
      (f := fun j =>
        basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
      (basisScalingLinearEquiv_two_update_pairwise
        (K := K) (W := W) (b := b) (i := i) (t := t))
      (g := dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)))

omit [Invertible (2 : K)] in
/-- A determinant-one basis scaling factors as the noncommutative product of the canonical `2×2`
determinant-one blocks supported on a distinguished basis line and each other basis line. -/
theorem basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ)
    (hprod : (∏ j, t j) = 1) :
    basisScalingLinearEquiv (K := K) (W := W) b t =
      (Finset.univ.erase i).noncommProd
        (fun j =>
          basisScalingLinearEquiv (K := K) (W := W) b
            (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
        (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := t)) := by
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hmul :
      t i * ((Finset.univ.erase i).prod fun j => t j) = ∏ j, t j := by
    simpa using (Finset.mul_prod_erase (s := Finset.univ) (f := t) hi)
  have hmul_one :
      t i * ((Finset.univ.erase i).prod fun j => t j) = 1 := by
    simpa [hprod] using hmul
  have hbase : t i = (Finset.univ.erase i).prod fun j => (t j)⁻¹ := by
    have hbase' : t i = ((Finset.univ.erase i).prod fun j => t j)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp hmul_one
    simpa [Finset.prod_inv_distrib] using hbase'
  exact basisScalingLinearEquiv_eq_noncommProd_two_update_of_base
    (K := K) (W := W) (b := b) (i := i) (t := t) hbase

omit [Invertible (2 : K)] in
/-- Transporting the determinant-one diagonal factorization to `SO(W* × W)` factors the
corresponding Levi element into canonical `2×2` determinant-one blocks. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ)
    (hprod : (∏ j, t j) = 1) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) =
      (Finset.univ.erase i).noncommProd
        (fun j =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
        (by
          intro j hj k hk hjk
          exact
            (basisScalingLinearEquiv_two_update_pairwise
              (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
              (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))) := by
  exact dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_noncommProd_two_update_of_base
    (K := K) (W := W) (b := b) (i := i) (t := t)
    ((by
      have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
      have hmul :
          t i * ((Finset.univ.erase i).prod fun j => t j) = ∏ j, t j := by
        simpa using (Finset.mul_prod_erase (s := Finset.univ) (f := t) hi)
      have hmul_one :
          t i * ((Finset.univ.erase i).prod fun j => t j) = 1 := by
        simpa [hprod] using hmul
      have hbase' : t i = ((Finset.univ.erase i).prod fun j => t j)⁻¹ :=
        (mul_eq_one_iff_eq_inv).mp hmul_one
      simpa [Finset.prod_inv_distrib] using hbase') : _)

omit [Invertible (2 : K)] in
/-- If the total basis scaling is a square, split it as a square line scaling on a distinguished
basis line times a determinant-one diagonal factorization. -/
theorem basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) (u : Kˣ)
    (hprod : (∏ j, t j) = u ^ 2) :
    basisScalingLinearEquiv (K := K) (W := W) b t =
      lineScalingLinearEquiv (f := b.coord i) (w := b i)
          (by simp [Module.Basis.coord_apply]) (u ^ 2) *
        (Finset.univ.erase i).noncommProd
          (fun j =>
            basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
          (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := t)) := by
  let s : ι → Kˣ := Function.update t i (t i / u ^ 2)
  have hsprod : (∏ j, s j) = 1 := by
    have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have hsupdate :
        (∏ j, s j) = (t i / u ^ 2) * (Finset.univ.erase i).prod fun j => t j := by
      simpa only [s, Finset.erase_eq] using
        (Finset.prod_update_of_mem (s := Finset.univ) (i := i) hi t (t i / u ^ 2))
    calc
      (∏ j, s j) = (t i / u ^ 2) * (Finset.univ.erase i).prod fun j => t j := hsupdate
      _ = (t i / u ^ 2) * ((∏ j, t j) / t i) := by
        rw [Finset.prod_erase_eq_div (s := Finset.univ) (f := t) hi]
      _ = 1 := by
        rw [hprod]
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hsplit : t = (Function.update (1 : ι → Kˣ) i (u ^ 2)) * s := by
    funext k
    apply Units.ext
    by_cases hki : k = i
    · subst hki
      simp [s, Function.update, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    · simp [s, Function.update, hki]
  have hsblocks :
      (Finset.univ.erase i).noncommProd
          (fun j =>
            basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (s j)) i (s j)⁻¹))
          (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := s)) =
        (Finset.univ.erase i).noncommProd
          (fun j =>
            basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
          (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := t)) := by
    refine Finset.noncommProd_congr rfl ?_
      (basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := s))
    · intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [s, Function.update, hji]
  calc
    basisScalingLinearEquiv (K := K) (W := W) b t =
        basisScalingLinearEquiv (K := K) (W := W) b
          ((Function.update (1 : ι → Kˣ) i (u ^ 2)) * s) := by
            rw [hsplit]
    _ = basisScalingLinearEquiv (K := K) (W := W) b (Function.update (1 : ι → Kˣ) i (u ^ 2)) *
          basisScalingLinearEquiv (K := K) (W := W) b s := by
            rw [basisScalingLinearEquiv_mul]
    _ = lineScalingLinearEquiv (f := b.coord i) (w := b i)
          (by simp [Module.Basis.coord_apply]) (u ^ 2) *
          basisScalingLinearEquiv (K := K) (W := W) b s := by
            rw [basisScalingLinearEquiv_update_eq_lineScalingLinearEquiv]
    _ = lineScalingLinearEquiv (f := b.coord i) (w := b i)
          (by simp [Module.Basis.coord_apply]) (u ^ 2) *
          (Finset.univ.erase i).noncommProd
            (fun j =>
              basisScalingLinearEquiv (K := K) (W := W) b
                (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
            (basisScalingLinearEquiv_two_update_pairwise
              (K := K) (W := W) (b := b) (i := i) (t := t)) := by
              rw [basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one
                    (K := K) (W := W) (b := b) (i := i) (t := s) hsprod,
                  hsblocks]

omit [Invertible (2 : K)] in
/-- Transporting a square-determinant basis scaling to `SO(W* × W)` splits it into a square line
scaling on a distinguished basis line times the determinant-one diagonal factorization. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) (u : Kˣ)
    (hprod : (∏ j, t j) = u ^ 2) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := b.coord i) (w := b i)
          (by simp [Module.Basis.coord_apply]) (u ^ 2)) *
        (Finset.univ.erase i).noncommProd
          (fun j =>
            dualProdSpecialOrthogonalOfLinearEquiv (K := K)
              (basisScalingLinearEquiv (K := K) (W := W) b
                (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
          (by
            intro j hj k hk hjk
            exact
              (basisScalingLinearEquiv_two_update_pairwise
                (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
                (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))) := by
  let H := dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)
  have hpair :=
    basisScalingLinearEquiv_two_update_pairwise (K := K) (W := W) (b := b) (i := i) (t := t)
  calc
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) =
      H (basisScalingLinearEquiv (K := K) (W := W) b t) := by rfl
    _ = H
          (lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2) *
            (Finset.univ.erase i).noncommProd
              (fun j =>
                basisScalingLinearEquiv (K := K) (W := W) b
                  (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
              hpair) := by
                rw [basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
                  (K := K) (W := W) (b := b) (i := i) (t := t) (u := u) hprod]
    _ = H (lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2)) *
          H ((Finset.univ.erase i).noncommProd
              (fun j =>
                basisScalingLinearEquiv (K := K) (W := W) b
                  (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
              hpair) := by
                rw [MonoidHom.map_mul]
    _ = dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2)) *
          (Finset.univ.erase i).noncommProd
            (fun j =>
              dualProdSpecialOrthogonalOfLinearEquiv (K := K)
                (basisScalingLinearEquiv (K := K) (W := W) b
                  (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
            (by
              intro j hj k hk hjk
              exact (hpair hj hk hjk).map H) := by
                simpa [H, dualProdSpecialOrthogonalOfLinearEquivHom_apply] using
                  (Finset.map_noncommProd (s := Finset.univ.erase i)
                    (f := fun j =>
                      basisScalingLinearEquiv (K := K) (W := W) b
                        (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹))
                    hpair (g := H))

omit [Invertible (2 : K)] in
/-- Relative to a chosen basis, any linear equivalence with square determinant factors as basis
transvections, a basis scaling with the same square determinant, and basis transvections. -/
theorem linearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
    (b : Module.Basis ι K W) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (t : ι → Kˣ),
      (∏ j, t j) = u ^ 2 ∧
      e =
        (L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod *
          basisScalingLinearEquiv (K := K) (W := W) b t *
          (L'.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod := by
  let M : Matrix ι ι K := LinearMap.toMatrix b b (e : W →ₗ[K] W)
  rcases Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M with
    ⟨L, L', D, hM⟩
  have hMdet : Matrix.det M = (u : K) ^ 2 := by
    calc
      Matrix.det M = LinearMap.det (e : W →ₗ[K] W) := by
        simpa [M] using (LinearMap.det_toMatrix b (e : W →ₗ[K] W))
      _ = (u : K) ^ 2 := by
        simpa [LinearEquiv.coe_det] using congrArg (fun z : Kˣ => (z : K)) hdet
  have hdiagdet : Matrix.det (Matrix.diagonal D) = (u : K) ^ 2 := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod, one_mul] at hMdet
    simpa using hMdet
  have hdiagdet_ne_zero : Matrix.det (Matrix.diagonal D) ≠ 0 := by
    rw [hdiagdet]
    exact pow_ne_zero 2 u.ne_zero
  have hDne : ∀ j, D j ≠ 0 := by
    intro j hj
    apply hdiagdet_ne_zero
    rw [Matrix.det_diagonal, Finset.prod_eq_zero_iff]
    exact ⟨j, Finset.mem_univ j, hj⟩
  let t : ι → Kˣ := fun j => Units.mk0 (D j) (hDne j)
  have htprod : (∏ j, t j) = u ^ 2 := by
    apply Units.ext
    simpa [t, Matrix.det_diagonal] using hdiagdet
  refine ⟨L, L', t, htprod, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix b b).injective
  calc
    LinearMap.toMatrix b b (e : W →ₗ[K] W) = M := by rfl
    _ = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod := hM
    _ = LinearMap.toMatrix b b
          ((((L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod : W ≃ₗ[K] W) *
              basisScalingLinearEquiv (K := K) (W := W) b t *
              ((L'.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod : W ≃ₗ[K] W)) :
            W ≃ₗ[K] W) := by
          have hdiag :
              LinearMap.toMatrix b b
                  ((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W) =
                Matrix.diagonal D := by
            rw [basisScalingLinearEquiv_toMatrix]
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [Matrix.diagonal, t]
            · simp [Matrix.diagonal, hij, t]
          simpa [LinearMap.toMatrix_mul,
            list_prod_basisTransvectionLinearEquiv_toMatrix (K := K) (W := W) (b := b),
            hdiag, Matrix.mul_assoc]

omit [Invertible (2 : K)] in
/-- Transporting the higher-rank square-determinant factorization to `SO(W* × W)` expresses any
such Levi element as basis transvections, a square-determinant basis scaling, and basis
transvections. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
    (b : Module.Basis ι K W) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (t : ι → Kˣ),
      (∏ j, t j) = u ^ 2 ∧
      dualProdSpecialOrthogonalOfLinearEquiv (K := K) e =
        (L.map (fun s =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod *
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisScalingLinearEquiv (K := K) (W := W) b t) *
          (L'.map (fun s =>
            dualProdSpecialOrthogonalOfLinearEquiv (K := K)
              (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod := by
  rcases
      linearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
        (K := K) (W := W) (b := b) (e := e) (u := u) hdet with
    ⟨L, L', t, htprod, he⟩
  let H := dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)
  refine ⟨L, L', t, htprod, ?_⟩
  rw [he]
  change H
      (((L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod : W ≃ₗ[K] W) *
        basisScalingLinearEquiv (K := K) (W := W) b t *
        ((L'.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod : W ≃ₗ[K] W)) =
    (L.map (fun s =>
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) *
      (L'.map (fun s =>
        dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod
  have hmapLprod :
      (List.map (⇑H) (List.map (basisTransvectionLinearEquiv (K := K) (W := W) b) L)).prod =
        (List.map (fun s =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisTransvectionLinearEquiv (K := K) (W := W) b s)) L).prod := by
    simpa [Function.comp_def, H, dualProdSpecialOrthogonalOfLinearEquivHom_apply] using
      congrArg List.prod
        (List.map_map (⇑H) (basisTransvectionLinearEquiv (K := K) (W := W) b) L)
  have hmapL'prod :
      (List.map (⇑H) (List.map (basisTransvectionLinearEquiv (K := K) (W := W) b) L')).prod =
        (List.map (fun s =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisTransvectionLinearEquiv (K := K) (W := W) b s)) L').prod := by
    simpa [Function.comp_def, H, dualProdSpecialOrthogonalOfLinearEquivHom_apply] using
      congrArg List.prod
        (List.map_map (⇑H) (basisTransvectionLinearEquiv (K := K) (W := W) b) L')
  rw [map_mul, map_mul, map_list_prod, map_list_prod, hmapLprod, hmapL'prod]
  rfl

omit [Invertible (2 : K)] in
/-- Combining the higher-rank matrix/transvection reduction with the square-determinant diagonal
reduction expresses any square-determinant Levi element in `SO(W* × W)` as basis transvections,
one chosen square line scaling, the canonical determinant-one `2 × 2` blocks, and basis
transvections. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_lineScalingLinearEquiv_mul_noncommProd_two_update_mul_list_basisTransvection_of_det_eq_sq
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (t : ι → Kˣ),
      (∏ j, t j) = u ^ 2 ∧
      dualProdSpecialOrthogonalOfLinearEquiv (K := K) e =
        (L.map (fun s =>
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod *
          dualProdSpecialOrthogonalOfLinearEquiv (K := K)
            (lineScalingLinearEquiv (f := b.coord i) (w := b i)
              (by simp [Module.Basis.coord_apply]) (u ^ 2)) *
          (Finset.univ.erase i).noncommProd
            (fun j =>
              dualProdSpecialOrthogonalOfLinearEquiv (K := K)
                (basisScalingLinearEquiv (K := K) (W := W) b
                  (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
            (by
              intro j hj k hk hjk
              exact
                (basisScalingLinearEquiv_two_update_pairwise
                  (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
                  (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W))) *
          (L'.map (fun s =>
            dualProdSpecialOrthogonalOfLinearEquiv (K := K)
              (basisTransvectionLinearEquiv (K := K) (W := W) b s))).prod := by
  rcases
      dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
        (K := K) (W := W) (b := b) (e := e) (u := u) hdet with
    ⟨L, L', t, htprod, he⟩
  refine ⟨L, L', t, htprod, ?_⟩
  rw [he,
    dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
      (K := K) (W := W) (b := b) (i := i) (t := t) (u := u) htprod]
  simp [mul_assoc]

omit [Invertible (2 : K)] in
/-- The canonical basis-diagonal `2 × 2` determinant-one block factors as four transvections. -/
theorem basisScalingLinearEquiv_two_update_eq_transvection_four
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    basisScalingLinearEquiv (K := K) (W := W) b
        (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹) =
      LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)) • b i))
        (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) *
      LinearEquiv.transvection (f := -(b.coord i)) (v := ((-1 : K) • b j))
        (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) *
      LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)⁻¹) • b i))
        (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) *
      LinearEquiv.transvection (f := -(b.coord i)) (v := ((a : K) • b j))
        (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) := by
  rw [basisScalingLinearEquiv_two_update (K := K) (W := W) (b := b) hij a]
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij] using
    complementaryLineScalings_eq_transvection_four (K := K) (W := W)
      (f := b.coord i) (g := b.coord j) (w := b i) (u := b j)
      (by simp [Module.Basis.coord_apply])
      (by simp [Module.Basis.coord_apply])
      (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])
      (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) a

omit [Invertible (2 : K)] in
/-- Transporting the canonical basis-diagonal `2 × 2` block to `SO(W* × W)` yields the matching
four-transvection factorization in the orthogonal action. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_eq_transvection_four
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹)) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)) • b i))
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord i)) (v := ((-1 : K) • b j))
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)⁻¹) • b i))
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) *
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord i)) (v := ((a : K) • b j))
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) := by
  rw [basisScalingLinearEquiv_two_update (K := K) (W := W) (b := b) hij a]
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij] using
    dualProdSpecialOrthogonalOf_complementaryLineScalings_eq_transvection_four
      (K := K) (W := W)
      (f := b.coord i) (g := b.coord j) (w := b i) (u := b j)
      (by simp [Module.Basis.coord_apply])
      (by simp [Module.Basis.coord_apply])
      (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])
      (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) a

end BasisScaling

/-- On a chosen split line inside `W* × W`, the reflection attached to
`(-c⁻¹ f, c w)` has an explicit coordinate formula. -/
theorem pinLinearRepresentation_apply_iota_of_dualProd_scaled_neg_dual_eq_one
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (c : Kˣ)
    (d : Module.Dual K W) (u : W) :
    pinLinearRepresentation (Q := QuadraticForm.dualProd K W)
        (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
          (-(((c : K)⁻¹) • f), (c : K) • w)
          (by simp [QuadraticForm.dualProd, hf]))
        (d, u) =
      (((d w - f u / ((c : K) ^ 2) : K) • f - d),
        -((((c : K) ^ 2) * d w - f u) : K) • w - u) := by
  rw [pinLinearRepresentation_apply_iota_of_dualProd_neg_dual_eq_one
    (K := K) (W := W) (f := ((c : K)⁻¹) • f) (w := (c : K) • w)
    (by simp [hf]) (d := d) (u := u)]
  apply Prod.ext
  · ext x
    simp [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    field_simp [c.ne_zero]
  · simp [smul_eq_mul, div_eq_mul_inv, hf, mul_assoc, mul_left_comm, mul_comm]
    rw [smul_smul]
    congr 1
    field_simp [c.ne_zero]

/-- Two reflections coming from the same split line act as a square scaling on that line and fix
the complementary kernels. -/
theorem spinSpecialOrthogonalPairGenerator_apply_dualProd_lineScaling
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (a b : Kˣ)
    (d : Module.Dual K W) (u : W) :
    (spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
        (-(((a : K)⁻¹) • f), (a : K) • w)
        (-(((b : K)⁻¹) • f), (b : K) • w)
        (by simp [QuadraticForm.dualProd, hf])
        (by simp [QuadraticForm.dualProd, hf])).1 (d, u) =
      (d + ((((b : K) / a) ^ 2 - 1) * d w : K) • f,
        u + ((((a : K) / b) ^ 2 - 1) * f u : K) • w) := by
  rw [coe_spinSpecialOrthogonalPairGenerator, QuadraticMap.IsometryEquiv.mul_apply,
    pinIsometryRepresentation_apply, pinIsometryEquiv_apply]
  have hfirst :
      ((pinIsometryRepresentation (Q := QuadraticForm.dualProd K W))
          (pinIotaOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
            (-(((b : K)⁻¹) • f), (b : K) • w)
            (by simp [QuadraticForm.dualProd, hf]))) (d, u) =
        (((d w - f u / ((b : K) ^ 2) : K) • f - d),
          -((((b : K) ^ 2) * d w - f u) : K) • w - u) := by
    simpa [pinIsometryRepresentation_apply, pinIsometryEquiv_apply] using
      (pinLinearRepresentation_apply_iota_of_dualProd_scaled_neg_dual_eq_one
        (K := K) (W := W) (f := f) (w := w) hf (c := b) (d := d) (u := u))
  rw [hfirst]
  rw [pinLinearRepresentation_apply_iota_of_dualProd_scaled_neg_dual_eq_one
    (K := K) (W := W) (f := f) (w := w) hf (c := a)
    (d := ((d w - f u / ((b : K) ^ 2) : K) • f - d))
    (u := -((((b : K) ^ 2) * d w - f u) : K) • w - u)]
  apply Prod.ext
  · ext x
    simp [smul_eq_mul, div_eq_mul_inv, hf, sub_eq_add_neg,
      mul_assoc, mul_left_comm, mul_comm]
    field_simp [a.ne_zero, b.ne_zero]
    ring
  · simp [smul_eq_mul, div_eq_mul_inv, hf, sub_eq_add_neg]
    let p : K := -(((b : K) ^ 2) * d w) + ((a : K) ^ 2) * (f u * (((b : K) ^ 2)⁻¹))
    let q : K := f u + -(((b : K) ^ 2) * d w)
    change p • w + (u + -(q • w)) = u + ((((a : K) * (b : K)⁻¹) ^ 2 + -1) * f u : K) • w
    have hcoef : p - q = ((((a : K) * (b : K)⁻¹) ^ 2 + -1) * f u : K) := by
      simp [p, q, pow_two, mul_assoc, mul_left_comm, mul_comm]
      field_simp [a.ne_zero, b.ne_zero]
      ring
    calc
      p • w + (u + -(q • w)) = u + (p - q) • w := by
        simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm]
      _ = u + ((((a : K) * (b : K)⁻¹) ^ 2 + -1) * f u : K) • w := by rw [hcoef]

/-- The pair generator built from two norm-`-1` vectors on a chosen split line is exactly the
transport of the corresponding square line scaling in `GL(W)`. -/
theorem spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (a b : Kˣ) :
    spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
        (-(((a : K)⁻¹) • f), (a : K) • w)
        (-(((b : K)⁻¹) • f), (b : K) • w)
        (by simp [QuadraticForm.dualProd, hf])
        (by simp [QuadraticForm.dualProd, hf]) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf ((a / b) ^ 2)) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rcases x with ⟨d, u⟩
  rw [spinSpecialOrthogonalPairGenerator_apply_dualProd_lineScaling
    (K := K) (W := W) (f := f) (w := w) hf (a := a) (b := b) (d := d) (u := u)]
  rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_lineScalingLinearEquiv
    (K := K) (W := W) (f := f) (w := w) hf (t := (a / b) ^ 2) (d := d) (u := u)]
  apply Prod.ext
  · ext y
    simp [smul_eq_mul, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
  · simp [smul_eq_mul, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Every square line scaling on a chosen split line already lies in the ambient spin image. -/
theorem dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_sq_mem_range
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf (t ^ 2)) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W)) := by
  have hpair :
      spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
          (-(((t : K)⁻¹) • f), (t : K) • w)
          (-f, w)
          (by simp [QuadraticForm.dualProd, hf])
          (by simp [QuadraticForm.dualProd, hf]) ∈
        MonoidHom.range
          (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W)) := by
    exact spinSpecialOrthogonalPairGeneratorSet_subset_range (Q := QuadraticForm.dualProd K W)
      ⟨⟨((-(((t : K)⁻¹) • f), (t : K) • w), (-f, w)),
          by simp [QuadraticForm.dualProd, hf]⟩, rfl⟩
  have hEq :
      spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
          (-(((t : K)⁻¹) • f), (t : K) • w)
          (-f, w)
          (by simp [QuadraticForm.dualProd, hf])
          (by simp [QuadraticForm.dualProd, hf]) =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (lineScalingLinearEquiv (f := f) (w := w) hf (t ^ 2)) := by
    simpa using
      (spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv
        (K := K) (W := W) (f := f) (w := w) hf (a := t) (b := (1 : Kˣ)))
  exact hEq ▸ hpair

/-- Conjugating the explicit transvection unit by the chosen square-scaling spin element rescales the
transvection parameter by the square torus weight. This is the internal Clifford-algebra version of
the chosen-line torus action. -/
theorem spinIotaPairOfQuadraticEqNegOne_conj_dualProdTransvectionCliffordUnit
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (t : Kˣ)
    (δ : Module.Dual K W) (hδ : δ w = 0) :
    let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
    let s : spinGroup Qd :=
      spinIotaPairOfQuadraticEqNegOne (Q := Qd)
        (-(((t : K)⁻¹) • f), (t : K) • w) (-f, w)
        (by simpa [Qd, QuadraticForm.dualProd, hf])
        (by simpa [Qd, QuadraticForm.dualProd, hf])
    spinConjAlgEquiv (Q := Qd) s
        (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
            (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd)) =
      (((dualProdTransvectionCliffordUnit (K := K) (W := W) (((t : K) ^ 2) • δ) w
          (by simpa [smul_eq_mul, hδ]) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd)) := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let s : spinGroup Qd :=
    spinIotaPairOfQuadraticEqNegOne (Q := Qd)
      (-(((t : K)⁻¹) • f), (t : K) • w) (-f, w)
      (by simpa [Qd, QuadraticForm.dualProd, hf])
      (by simpa [Qd, QuadraticForm.dualProd, hf])
  let aδ : Module.Dual K W × W := (δ, 0)
  let b : Module.Dual K W × W := (0, w)
  have hs_eq :
      spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Qd) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (lineScalingLinearEquiv (f := f) (w := w) hf (t ^ 2)) := by
    simpa [Qd, s, spinSpecialOrthogonalPairGenerator] using
      (spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv
        (K := K) (W := W) (f := f) (w := w) hf (a := t) (b := (1 : Kˣ)))
  have haδ :
      (dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf (t ^ 2))).1 aδ = aδ := by
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_lineScalingLinearEquiv
      (K := K) (W := W) (f := f) (w := w) hf (t := t ^ 2) (d := δ) (u := 0)]
    apply Prod.ext
    · ext x
      simp [aδ, hδ]
    · simp [aδ]
  have hb :
      (dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (lineScalingLinearEquiv (f := f) (w := w) hf (t ^ 2))).1 b =
          (0, ((t : K) ^ 2) • w) := by
    rw [dualProdSpecialOrthogonalOfLinearEquiv_apply_lineScalingLinearEquiv
      (K := K) (W := W) (f := f) (w := w) hf (t := t ^ 2) (d := 0) (u := w)]
    have hw :
        ((0 : Module.Dual K W), w + ((((↑(t ^ 2) : K) - 1) * f w) : K) • w) =
          (0, ((t : K) ^ 2) • w) := by
      apply Prod.ext
      · ext x
        simp
      · calc
          w + ((((↑(t ^ 2) : K) - 1) * f w) : K) • w = w + (((↑(t ^ 2) : K) - 1) : K) • w := by
            rw [hf, mul_one]
          _ = (((1 : K) + ((↑(t ^ 2) : K) - 1)) : K) • w := by
            rw [add_smul, one_smul]
          _ = ((t : K) ^ 2) • w := by simp
    simpa [b, hf] using hw
  have hδfixed :
      spinLinearRepresentation (Q := Qd) s aδ = aδ := by
    have h :=
      congrArg (fun e : Qd.specialOrthogonalGroup => e.1 aδ) hs_eq
    simpa [Qd, aδ, spinLinearRepresentation_apply,
      coe_spinSpecialOrthogonalRepresentationFiniteDimensional,
      spinIsometryRepresentation_apply, spinIsometryEquiv_apply] using h.trans haδ
  have hwscaled :
      spinLinearRepresentation (Q := Qd) s b = (0, ((t : K) ^ 2) • w) := by
    have h :=
      congrArg (fun e : Qd.specialOrthogonalGroup => e.1 b) hs_eq
    simpa [Qd, b, spinLinearRepresentation_apply,
      coe_spinSpecialOrthogonalRepresentationFiniteDimensional,
      spinIsometryRepresentation_apply, spinIsometryEquiv_apply] using h.trans hb
  have hιδ :
      spinConjAlgEquiv (Q := Qd) s (CliffordAlgebra.ι Qd aδ) =
        CliffordAlgebra.ι Qd aδ := by
    rw [spinConjAlgEquiv_apply, ← spinLinearEquiv_ι (Q := Qd) s aδ,
      ← spinLinearRepresentation_apply (Q := Qd) s, hδfixed]
  have hιw :
      spinConjAlgEquiv (Q := Qd) s (CliffordAlgebra.ι Qd b) =
        CliffordAlgebra.ι Qd (0, ((t : K) ^ 2) • w) := by
    rw [spinConjAlgEquiv_apply, ← spinLinearEquiv_ι (Q := Qd) s b,
      ← spinLinearRepresentation_apply (Q := Qd) s, hwscaled]
  rw [coe_dualProdTransvectionCliffordUnit, coe_dualProdTransvectionCliffordUnit]
  calc
    spinConjAlgEquiv (Q := Qd) s (1 + CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd b) =
        1 + CliffordAlgebra.ι Qd aδ * CliffordAlgebra.ι Qd (0, ((t : K) ^ 2) • w) := by
          rw [map_add, map_one, map_mul, hιδ, hιw]
    _ = 1 + CliffordAlgebra.ι Qd ((((t : K) ^ 2) • δ), 0) * CliffordAlgebra.ι Qd b := by
      have ha :
          ((((t : K) ^ 2) • δ), (0 : W)) = ((t : K) ^ 2) • aδ := by
        ext <;> simp [aδ]
      have hb :
          ((0 : Module.Dual K W), ((t : K) ^ 2) • w) = ((t : K) ^ 2) • b := by
        ext <;> simp [b]
      rw [ha, hb, map_smul, map_smul]
      simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- In the split hyperbolic form, the pair generator built from `(-(f + δ), w)` and `(-f, w)`
has an explicit coordinate action on arbitrary `(d, u)`. This packages the basic hyperbolic
transvection pattern used by the split-rank image theorems. -/
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
hyperbolic transvection pattern used by the split-rank image theorems. -/
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

omit [Invertible (2 : R)] in
/-- If `a` is isotropic and orthogonal to a norm-`-1` vector `c`, then
`1 + ι(a)ι(c)` is already a spin element. Algebraically it is
`-(ι(c-a)ι(c))`, a product of two norm-`-1` vector factors up to the scalar
spin element `-1`. -/
theorem one_add_iota_mul_iota_mem_spinGroup_of_isotropic_ortho_norm_neg_one
    (a c : M) (ha : Q a = 0) (hc : Q c = -1)
    (hac : QuadraticMap.polar Q a c = 0) :
    (1 + CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c : CliffordAlgebra Q) ∈
      spinGroup Q := by
  have hcsub : Q (c - a) = -1 := by
    have hca : QuadraticMap.polar Q c a = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hac
    rw [sub_eq_add_neg]
    rw [QuadraticMap.map_add Q c (-a)]
    rw [QuadraticMap.map_neg]
    rw [QuadraticMap.polar_neg_right]
    simp [hc, ha, hca]
  have hspinPair :
      (CliffordAlgebra.ι Q (c - a) * CliffordAlgebra.ι Q c : CliffordAlgebra Q) ∈
        spinGroup Q := by
    exact (spinIotaPairOfQuadraticEqNegOne (Q := Q) (c - a) c hcsub hc).prop
  have hneg : (-1 : CliffordAlgebra Q) ∈ spinGroup Q :=
    neg_one_mem_spinGroup_of_quadratic_eq_neg_one (Q := Q) c hc
  have hprod :
      (-1 : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q (c - a) * CliffordAlgebra.ι Q c) ∈ spinGroup Q := by
    exact (spinGroup Q).mul_mem hneg hspinPair
  convert hprod using 1
  rw [map_sub, sub_mul, CliffordAlgebra.ι_sq_scalar]
  simp [hc, sub_eq_add_neg, add_comm]

private theorem commutator_square_zero {A : Type*} [Ring A] (x y : A)
    (hx : x * x = 0) (hy : y * y = 0)
    (hxyx : x * y * x = 0) (hyxy : y * x * y = 0) :
    (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + (x * y - y * x) := by
  simp [sub_eq_add_neg, mul_add, add_mul, hx, hy, hxyx, hyxy, mul_assoc]
  abel

/-- If two orthogonal isotropic vectors `a` and `b` have a common orthogonal
norm-`-1` auxiliary vector `c`, then the unipotent Clifford element
`1 + ι(a)ι(b)` lies in the spin group. This is the commutator
`[1+ι(a)ι(c), 1+(1/2)ι(b)ι(c)]`. -/
theorem one_add_iota_mul_iota_mem_spinGroup_of_common_orthogonal_norm_neg_one
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (a b c : M) (ha : Q a = 0) (hb : Q b = 0) (hc : Q c = -1)
    (hab : QuadraticMap.polar Q a b = 0)
    (hac : QuadraticMap.polar Q a c = 0)
    (hbc : QuadraticMap.polar Q b c = 0) :
    (1 + CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b : CliffordAlgebra Q) ∈
      spinGroup Q := by
  let A : CliffordAlgebra Q := CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c
  let B : CliffordAlgebra Q := ((2 : K)⁻¹) •
    (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c)
  have hrootA : (1 + A : CliffordAlgebra Q) ∈ spinGroup Q := by
    dsimp [A]
    exact one_add_iota_mul_iota_mem_spinGroup_of_isotropic_ortho_norm_neg_one
      (Q := Q) a c ha hc hac
  have hrootB : (1 + B : CliffordAlgebra Q) ∈ spinGroup Q := by
    dsimp [B]
    simpa [map_smul, Algebra.smul_def, mul_assoc] using
      one_add_iota_mul_iota_mem_spinGroup_of_isotropic_ortho_norm_neg_one
        (Q := Q) (((2 : K)⁻¹) • b) c
        (by simp [QuadraticMap.map_smul, hb]) hc
        (by simp [QuadraticMap.polar_smul_left, hbc])
  have hrootAneg : (1 - A : CliffordAlgebra Q) ∈ spinGroup Q := by
    dsimp [A]
    simpa [sub_eq_add_neg, map_neg, neg_mul] using
      one_add_iota_mul_iota_mem_spinGroup_of_isotropic_ortho_norm_neg_one
        (Q := Q) (-a) c (by simp [QuadraticMap.map_neg, ha]) hc
        (by simp [QuadraticMap.polar_neg_left, hac])
  have hrootBneg : (1 - B : CliffordAlgebra Q) ∈ spinGroup Q := by
    dsimp [B]
    simpa [sub_eq_add_neg, map_smul, Algebra.smul_def, mul_assoc] using
      one_add_iota_mul_iota_mem_spinGroup_of_isotropic_ortho_norm_neg_one
        (Q := Q) (-(((2 : K)⁻¹) • b)) c
        (by simp [QuadraticMap.map_neg, QuadraticMap.map_smul, hb]) hc
        (by simp [QuadraticMap.polar_neg_left, QuadraticMap.polar_smul_left, hbc])
  have hprod :
      ((1 + A) * (1 + B) * (1 - A) * (1 - B) : CliffordAlgebra Q) ∈ spinGroup Q := by
    exact (spinGroup Q).mul_mem
      ((spinGroup Q).mul_mem ((spinGroup Q).mul_mem hrootA hrootB) hrootAneg) hrootBneg
  have hA2 : A * A = 0 := by
    dsimp [A]
    calc
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) =
          CliffordAlgebra.ι Q a *
            ((CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q c) := by
            simp only [mul_assoc]
      _ = CliffordAlgebra.ι Q a *
            ((-CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) * CliffordAlgebra.ι Q c) := by
            rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) c a]
            rw [show QuadraticMap.polar Q c a = 0 by
              simpa [QuadraticMap.polar_comm] using hac]
            simp
      _ = -((CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) *
            (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q c)) := by
            simp only [mul_assoc, neg_mul, mul_neg]
      _ = 0 := by
            rw [CliffordAlgebra.ι_sq_scalar (Q := Q) a]
            simp [ha]
  have hBcore2 :
      (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) *
          (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) = 0 := by
    calc
      (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) *
          (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) =
          CliffordAlgebra.ι Q b *
            ((CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q c) := by
            simp only [mul_assoc]
      _ = CliffordAlgebra.ι Q b *
            ((-CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) * CliffordAlgebra.ι Q c) := by
            rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) c b]
            rw [show QuadraticMap.polar Q c b = 0 by
              simpa [QuadraticMap.polar_comm] using hbc]
            simp
      _ = -((CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q b) *
            (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q c)) := by
            simp only [mul_assoc, neg_mul, mul_neg]
      _ = 0 := by
            rw [CliffordAlgebra.ι_sq_scalar (Q := Q) b]
            simp [hb]
  have hB2 : B * B = 0 := by
    dsimp [B]
    simp [hBcore2]
  have hAB :
      A * B = ((2 : K)⁻¹) • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
    dsimp [A, B]
    rw [mul_smul_comm]
    congr 1
    calc
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) *
          (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) =
        CliffordAlgebra.ι Q a *
          ((CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q c) := by
          simp [mul_assoc]
      _ = CliffordAlgebra.ι Q a *
          ((-CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) * CliffordAlgebra.ι Q c) := by
          rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) c b]
          rw [show QuadraticMap.polar Q c b = 0 by
            simpa [QuadraticMap.polar_comm] using hbc]
          simp
      _ = -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q c) := by
          simp [mul_assoc]
      _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b := by
          rw [CliffordAlgebra.ι_sq_scalar, hc]
          simp
  have hBA :
      B * A = -(((2 : K)⁻¹) • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) := by
    dsimp [A, B]
    rw [smul_mul_assoc]
    rw [show (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) =
        -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) by
      calc
        (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) *
            (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) =
          CliffordAlgebra.ι Q b *
            ((CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q c) := by
            simp [mul_assoc]
        _ = CliffordAlgebra.ι Q b *
            ((-CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) * CliffordAlgebra.ι Q c) := by
            rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) c a]
            rw [show QuadraticMap.polar Q c a = 0 by
              simpa [QuadraticMap.polar_comm] using hac]
            simp
        _ = -(CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a) *
            (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q c) := by
            simp [mul_assoc]
        _ = CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a := by
            rw [CliffordAlgebra.ι_sq_scalar, hc]
            simp
        _ = -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
            rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) b a]
            rw [show QuadraticMap.polar Q b a = 0 by
              simpa [QuadraticMap.polar_comm] using hab]
            simp]
    simp
  have hcoreA : (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * A = 0 := by
    dsimp [A]
    calc
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q c) =
        CliffordAlgebra.ι Q a *
          ((CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q c) := by
          simp only [mul_assoc]
      _ = CliffordAlgebra.ι Q a *
          ((-CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q c) := by
          rw [CliffordAlgebra.ι_mul_ι_comm (Q := Q) b a]
          rw [show QuadraticMap.polar Q b a = 0 by
            simpa [QuadraticMap.polar_comm] using hab]
          simp
      _ = -((CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) *
          (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c)) := by
          simp only [mul_assoc, neg_mul, mul_neg]
      _ = 0 := by
          rw [CliffordAlgebra.ι_sq_scalar (Q := Q) a]
          simp [ha]
  have hABA : A * B * A = 0 := by
    rw [hAB]
    rw [smul_mul_assoc]
    simp [hcoreA]
  have hcoreB : (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * B = 0 := by
    dsimp [B]
    rw [mul_smul_comm]
    simp only [smul_eq_zero]
    right
    calc
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) =
        CliffordAlgebra.ι Q a *
          ((CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q c) := by
          simp only [mul_assoc]
      _ = 0 := by
          rw [CliffordAlgebra.ι_sq_scalar (Q := Q) b]
          simp [hb]
  have hBAB : B * A * B = 0 := by
    rw [hBA]
    rw [neg_mul, smul_mul_assoc]
    simp [hcoreB]
  have hdiff : A * B - B * A = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b := by
    rw [hAB, hBA]
    rw [sub_eq_add_neg, neg_neg, ← add_smul]
    have hhalf : ((2 : K)⁻¹ + (2 : K)⁻¹ : K) = 1 := by
      field_simp [(isUnit_of_invertible (2 : K)).ne_zero]
      ring
    simp [hhalf]
  have heq :
      (1 + A) * (1 + B) * (1 - A) * (1 - B) =
        1 + CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b := by
    rw [commutator_square_zero A B hA2 hB2 hABA hBAB, hdiff]
  simpa [heq] using hprod

private theorem four_vector_product_eq_one_add_of_relations
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [Invertible (2 : K)]
    (a d b : A)
    (ha2 : a * a = 0) (hd2 : d * d = 0) (hb2 : b * b = 0)
    (had : a * d = -d * a) (hdb : d * b = -b * d)
    (hab : a * b + b * a = 1) :
    (a - d + b) * (a + b) * (a + (2 : K) • b) *
        (((2 : K)⁻¹) • a - d + b) =
      1 + d * b := by
  have hBA : b * a = 1 - a * b := by
    rw [← hab]
    abel
  have hDA : d * a = -a * d := by
    simpa using (congrArg Neg.neg had).symm
  have hBD : b * d = -d * b := by
    simpa using (congrArg Neg.neg hdb).symm
  have hp12 : (a - d + b) * (a + b) = 1 + a * d - d * b := by
    simp [sub_eq_add_neg, add_mul, mul_add, ha2, hb2, hBA, hDA, hdb]
    abel
  have had_a : a * d * a = 0 := by
    calc
      a * d * a = a * (d * a) := by rw [mul_assoc]
      _ = a * (-(a * d)) := by simpa [mul_neg] using congrArg (fun x => a * x) hDA
      _ = 0 := by rw [mul_neg, ← mul_assoc, ha2]; simp
  have hdb_b : d * b * b = 0 := by
    rw [mul_assoc, hb2]
    simp
  have hdb_a : d * b * a = d + a * d * b := by
    calc
      d * b * a = d * (b * a) := by rw [mul_assoc]
      _ = d * (1 - a * b) := by rw [hBA]
      _ = d - d * (a * b) := by simp [mul_sub]
      _ = d - (d * a) * b := by rw [mul_assoc]
      _ = d - (-(a * d)) * b := by
        simpa [neg_mul] using congrArg (fun x => d - x * b) hDA
      _ = d + a * d * b := by rw [neg_mul]; simp [mul_assoc, sub_eq_add_neg]
  have hp123 :
      (a - d + b) * (a + b) * (a + (2 : K) • b) =
        a + (2 : K) • b - d + a * d * b := by
    have h_ad_mul : (a * d) * (a + (2 : K) • b) = (2 : K) • (a * d * b) := by
      rw [mul_add, had_a, zero_add]
      rw [mul_smul_comm]
    have h_db_mul : (d * b) * (a + (2 : K) • b) = d + a * d * b := by
      have hdb_two : d * b * ((2 : K) • b) = 0 := by
        rw [mul_smul_comm, hdb_b, smul_zero]
      rw [mul_add, hdb_a, hdb_two, add_zero]
    rw [hp12]
    rw [sub_eq_add_neg]
    rw [add_mul, add_mul, one_mul]
    rw [h_ad_mul]
    rw [neg_mul, h_db_mul]
    module
  have hadb_a : a * d * b * a = a * d := by
    calc
      a * d * b * a = a * (d * b * a) := by simp [mul_assoc]
      _ = a * (d + a * d * b) := by rw [hdb_a]
      _ = a * d + a * (a * d * b) := by rw [mul_add]
      _ = a * d := by
        have haa : a * (a * d * b) = 0 := by
          calc
            a * (a * d * b) = (a * a) * d * b := by simp [mul_assoc]
            _ = 0 := by rw [ha2]; simp
        rw [haa, add_zero]
  have hadb_d : a * d * b * d = 0 := by
    calc
      a * d * b * d = a * d * (b * d) := by simp [mul_assoc]
      _ = a * d * (-(d * b)) := by
        simpa [mul_neg] using congrArg (fun x => a * d * x) hBD
      _ = -(a * d * (d * b)) := by rw [mul_neg]
      _ = 0 := by
        have hdd : a * d * (d * b) = 0 := by
          calc
            a * d * (d * b) = a * (d * d) * b := by simp [mul_assoc]
            _ = 0 := by rw [hd2]; simp
        rw [hdd, neg_zero]
  have hadb_b : a * d * b * b = 0 := by
    calc
      a * d * b * b = a * d * (b * b) := by simp [mul_assoc]
      _ = 0 := by rw [hb2, mul_zero]
  have ha_V : a * (((2 : K)⁻¹) • a - d + b) = -(a * d) + a * b := by
    simp [sub_eq_add_neg, mul_add, mul_smul_comm, ha2]
  have hb_V : ((2 : K) • b) * (((2 : K)⁻¹) • a - d + b) =
      b * a - (2 : K) • (b * d) := by
    simp [sub_eq_add_neg, mul_add, smul_mul_assoc, hb2, smul_smul, mul_comm,
      mul_left_comm, mul_assoc]
  have hd_V : d * (((2 : K)⁻¹) • a - d + b) =
      -(((2 : K)⁻¹) • (a * d)) + d * b := by
    simp [sub_eq_add_neg, mul_add, mul_smul_comm, hd2, hDA, smul_smul, mul_comm,
      mul_left_comm, mul_assoc]
  have hadb_V : (a * d * b) * (((2 : K)⁻¹) • a - d + b) =
      ((2 : K)⁻¹) • (a * d) := by
    have h1 : (a * d * b) * (((2 : K)⁻¹) • a) = ((2 : K)⁻¹) • (a * d) := by
      rw [mul_smul_comm, hadb_a]
    have h2neg : (a * d * b) * (-d) = 0 := by
      rw [mul_neg, hadb_d, neg_zero]
    have h3 : (a * d * b) * b = 0 := hadb_b
    rw [sub_eq_add_neg, mul_add, mul_add]
    rw [h1, h2neg, h3]
    simp
  rw [hp123]
  rw [sub_eq_add_neg]
  rw [add_mul, add_mul, add_mul]
  rw [ha_V, hb_V]
  rw [neg_mul, hd_V, hadb_V]
  rw [hBA, hBD]
  simp
  have hhalf : ((2 : K)⁻¹ + (2 : K)⁻¹ : K) = 1 := by
    field_simp [(isUnit_of_invertible (2 : K)).ne_zero]
    ring
  have hAD : -(a * d) + (2 : K)⁻¹ • (a * d) + (2 : K)⁻¹ • (a * d) = 0 := by
    calc
      -(a * d) + (2 : K)⁻¹ • (a * d) + (2 : K)⁻¹ • (a * d)
          = (-1 + ((2 : K)⁻¹ + (2 : K)⁻¹)) • (a * d) := by module
      _ = 0 := by rw [hhalf]; simp
  have hDB : (2 : K) • (d * b) + -(d * b) = d * b := by
    calc
      (2 : K) • (d * b) + -(d * b) = ((2 : K) + -1) • (d * b) := by module
      _ = d * b := by norm_num
  calc
    -(a * d) + a * b + (1 - a * b + (2 : K) • (d * b)) +
          (-(d * b) + (2 : K)⁻¹ • (a * d)) + (2 : K)⁻¹ • (a * d)
        =
        (a * b + (1 - a * b)) + ((2 : K) • (d * b) + -(d * b)) +
          (-(a * d) + (2 : K)⁻¹ • (a * d) + (2 : K)⁻¹ • (a * d)) := by
          abel
    _ = 1 + d * b := by rw [hAD, hDB]; simp

/-- The explicit hyperbolic transvection Clifford unit is a spin element whenever the two isotropic
vectors `(δ,0)` and `(0,w)` have a common orthogonal norm-`-1` auxiliary vector. -/
theorem dualProdTransvectionCliffordUnit_mem_spinGroup_of_common_orthogonal_norm_neg_one
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (c : Module.Dual K W × W)
    (hc : QuadraticForm.dualProd K W c = -1)
    (hac : QuadraticMap.polar (QuadraticForm.dualProd K W) (δ, 0) c = 0)
    (hbc : QuadraticMap.polar (QuadraticForm.dualProd K W) (0, w) c = 0) :
    (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        spinGroup (QuadraticForm.dualProd K W) := by
  simpa [coe_dualProdTransvectionCliffordUnit] using
    (one_add_iota_mul_iota_mem_spinGroup_of_common_orthogonal_norm_neg_one
      (Q := QuadraticForm.dualProd K W)
      (a := (δ, 0)) (b := (0, w)) (c := c)
      (by simp [QuadraticForm.dualProd])
      (by simp [QuadraticForm.dualProd]) hc
      (by simpa [QuadraticForm.dualProd, QuadraticMap.polar] using hδ)
      hac hbc)

/-- The explicit hyperbolic transvection Clifford unit is a spin element whenever the primal
direction has a dual coordinate equal to `1`. This covers every basis transvection, including
split rank two, without needing an auxiliary orthogonal basis direction. -/
theorem dualProdTransvectionCliffordUnit_mem_spinGroup_of_dual_apply_eq_one
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W]
    (δ f : Module.Dual K W) (w : W) (hδ : δ w = 0) (hf : f w = 1) :
    (((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        spinGroup (QuadraticForm.dualProd K W) := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let A : Module.Dual K W × W := (f, 0)
  let D : Module.Dual K W × W := (δ, 0)
  let B : Module.Dual K W × W := (0, w)
  let v1 : Module.Dual K W × W := A - D + B
  let v2 : Module.Dual K W × W := A + B
  let v3 : Module.Dual K W × W := A + (2 : K) • B
  let v4 : Module.Dual K W × W := ((2 : K)⁻¹) • A - D + B
  let u1 : (CliffordAlgebra Qd)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v1) (by
      change IsUnit (Qd v1)
      rw [show Qd v1 = 1 by simp [Qd, v1, A, D, B, QuadraticForm.dualProd, hδ, hf]]
      exact isUnit_one)).unit
  let u2 : (CliffordAlgebra Qd)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v2) (by
      change IsUnit (Qd v2)
      rw [show Qd v2 = 1 by simp [Qd, v2, A, B, QuadraticForm.dualProd, hf]]
      exact isUnit_one)).unit
  let u3 : (CliffordAlgebra Qd)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v3) (by
      change IsUnit (Qd v3)
      rw [show Qd v3 = 2 by simp [Qd, v3, A, B, QuadraticForm.dualProd, hf]]
      exact isUnit_of_invertible (2 : K))).unit
  let u4 : (CliffordAlgebra Qd)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v4) (by
      change IsUnit (Qd v4)
      rw [show Qd v4 = (2 : K)⁻¹ by
        simp [Qd, v4, A, D, B, QuadraticForm.dualProd, hδ, hf]]
      exact IsUnit.inv (isUnit_of_invertible (2 : K)))).unit
  have hu1 : (u1 : CliffordAlgebra Qd) = CliffordAlgebra.ι Qd v1 := by
    exact IsUnit.unit_spec
      (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v1) (by
        change IsUnit (Qd v1)
        rw [show Qd v1 = 1 by simp [Qd, v1, A, D, B, QuadraticForm.dualProd, hδ, hf]]
        exact isUnit_one))
  have hu2 : (u2 : CliffordAlgebra Qd) = CliffordAlgebra.ι Qd v2 := by
    exact IsUnit.unit_spec
      (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v2) (by
        change IsUnit (Qd v2)
        rw [show Qd v2 = 1 by simp [Qd, v2, A, B, QuadraticForm.dualProd, hf]]
        exact isUnit_one))
  have hu3 : (u3 : CliffordAlgebra Qd) = CliffordAlgebra.ι Qd v3 := by
    exact IsUnit.unit_spec
      (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v3) (by
        change IsUnit (Qd v3)
        rw [show Qd v3 = 2 by simp [Qd, v3, A, B, QuadraticForm.dualProd, hf]]
        exact isUnit_of_invertible (2 : K)))
  have hu4 : (u4 : CliffordAlgebra Qd) = CliffordAlgebra.ι Qd v4 := by
    exact IsUnit.unit_spec
      (CliffordAlgebra.isUnit_ι_of_isUnit (Q := Qd) (m := v4) (by
        change IsUnit (Qd v4)
        rw [show Qd v4 = (2 : K)⁻¹ by
          simp [Qd, v4, A, D, B, QuadraticForm.dualProd, hδ, hf]]
        exact IsUnit.inv (isUnit_of_invertible (2 : K))))
  have hu_lip : u1 * u2 * u3 * u4 ∈ lipschitzGroup Qd := by
    refine (lipschitzGroup Qd).mul_mem
      ((lipschitzGroup Qd).mul_mem ((lipschitzGroup Qd).mul_mem ?_ ?_) ?_) ?_
    · exact Subgroup.subset_closure ⟨v1, hu1⟩
    · exact Subgroup.subset_closure ⟨v2, hu2⟩
    · exact Subgroup.subset_closure ⟨v3, hu3⟩
    · exact Subgroup.subset_closure ⟨v4, hu4⟩
  have hfactor :
      (CliffordAlgebra.ι Qd v1 * CliffordAlgebra.ι Qd v2 *
            CliffordAlgebra.ι Qd v3 * CliffordAlgebra.ι Qd v4) =
        (1 + CliffordAlgebra.ι Qd D * CliffordAlgebra.ι Qd B) := by
    have ha2 : CliffordAlgebra.ι Qd A * CliffordAlgebra.ι Qd A = 0 := by
      rw [CliffordAlgebra.ι_sq_scalar]
      have hQA : Qd A = 0 := by simp [Qd, A, QuadraticForm.dualProd]
      rw [hQA]
      simp
    have hd2 : CliffordAlgebra.ι Qd D * CliffordAlgebra.ι Qd D = 0 := by
      rw [CliffordAlgebra.ι_sq_scalar]
      have hQD : Qd D = 0 := by simp [Qd, D, QuadraticForm.dualProd]
      rw [hQD]
      simp
    have hb2 : CliffordAlgebra.ι Qd B * CliffordAlgebra.ι Qd B = 0 := by
      rw [CliffordAlgebra.ι_sq_scalar]
      have hQB : Qd B = 0 := by simp [Qd, B, QuadraticForm.dualProd]
      rw [hQB]
      simp
    have had :
        CliffordAlgebra.ι Qd A * CliffordAlgebra.ι Qd D =
          -CliffordAlgebra.ι Qd D * CliffordAlgebra.ι Qd A := by
      rw [CliffordAlgebra.ι_mul_ι_comm (Q := Qd) A D]
      have hpolar : QuadraticMap.polar Qd A D = 0 := by
        simp [Qd, A, D, QuadraticMap.polar, QuadraticForm.dualProd]
      rw [hpolar]
      simp
    have hdb :
        CliffordAlgebra.ι Qd D * CliffordAlgebra.ι Qd B =
          -CliffordAlgebra.ι Qd B * CliffordAlgebra.ι Qd D := by
      rw [CliffordAlgebra.ι_mul_ι_comm (Q := Qd) D B]
      have hpolar : QuadraticMap.polar Qd D B = 0 := by
        simp [Qd, D, B, QuadraticMap.polar, QuadraticForm.dualProd, hδ]
      rw [hpolar]
      simp
    have hab :
        CliffordAlgebra.ι Qd A * CliffordAlgebra.ι Qd B +
            CliffordAlgebra.ι Qd B * CliffordAlgebra.ι Qd A = 1 := by
      rw [CliffordAlgebra.ι_mul_ι_comm (Q := Qd) B A]
      have hpolar : QuadraticMap.polar Qd B A = 1 := by
        simp [Qd, A, B, QuadraticMap.polar, QuadraticForm.dualProd, hf]
      rw [hpolar]
      simp
    simpa [v1, v2, v3, v4, map_add, map_sub, map_smul] using
      (four_vector_product_eq_one_add_of_relations
        (K := K) (A := CliffordAlgebra Qd)
        (a := CliffordAlgebra.ι Qd A) (d := CliffordAlgebra.ι Qd D)
        (b := CliffordAlgebra.ι Qd B) ha2 hd2 hb2 had hdb hab)
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · refine ⟨u1 * u2 * u3 * u4, hu_lip, ?_⟩
      change
        (u1 : CliffordAlgebra Qd) * (u2 : CliffordAlgebra Qd) *
            (u3 : CliffordAlgebra Qd) * (u4 : CliffordAlgebra Qd) =
          ((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
            (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd)
      rw [hu1, hu2, hu3, hu4]
      rw [hfactor]
      rw [coe_dualProdTransvectionCliffordUnit]
    · simpa [Qd] using
        dualProdTransvectionCliffordUnit_mem_unitary (K := K) (W := W) δ w hδ
  · simpa [Qd] using
      dualProdTransvectionCliffordUnit_mem_even (K := K) (W := W) δ w hδ

/-- Every basis-transvection Clifford unit is a genuine spin element. -/
theorem basisTransvectionCliffordUnit_mem_spinGroup
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    (((basisTransvectionCliffordUnit (K := K) (W := W) b t :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        spinGroup (QuadraticForm.dualProd K W) := by
  simpa [basisTransvectionCliffordUnit] using
    (dualProdTransvectionCliffordUnit_mem_spinGroup_of_dual_apply_eq_one
      (K := K) (W := W)
      (δ := -((t.c : K) • b.coord t.j)) (f := b.coord t.i) (w := b t.i)
      (hδ := by simp [Module.Basis.coord_apply, t.hij])
      (hf := by simp [Module.Basis.coord_apply]))

/-- Package the basis-transvection Clifford unit as a spin element. -/
noncomputable def basisTransvectionSpin
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    spinGroup (QuadraticForm.dualProd K W) :=
  ⟨(basisTransvectionCliffordUnit (K := K) (W := W) b t :
      (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ),
    basisTransvectionCliffordUnit_mem_spinGroup (K := K) (W := W) b t⟩

@[simp]
theorem coe_basisTransvectionSpin
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    ((basisTransvectionSpin (K := K) (W := W) b t :
      spinGroup (QuadraticForm.dualProd K W)) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      basisTransvectionCliffordUnit (K := K) (W := W) b t := rfl

/-- The basis-transvection spin lift maps to the corresponding split-special-orthogonal Levi
transvection. -/
theorem spinSpecialOrthogonalRepresentation_basisTransvectionSpin
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W)
        (basisTransvectionSpin (K := K) (W := W) b t) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t) := by
  let xU : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ :=
    basisTransvectionCliffordUnit (K := K) (W := W) b t
  let s : spinGroup (QuadraticForm.dualProd K W) :=
    basisTransvectionSpin (K := K) (W := W) b t
  change spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W) s =
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
      (basisTransvectionLinearEquiv (K := K) (W := W) b t)
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  apply cliffordIota_injective (Q := QuadraticForm.dualProd K W)
  have hUnits : spinGroup.toUnits s = xU := by
    ext
    rfl
  rw [coe_spinSpecialOrthogonalRepresentationFiniteDimensional]
  rw [spinIsometryRepresentation_apply, spinIsometryEquiv_apply]
  rw [spinLinearRepresentation_apply, spinLinearEquiv_ι]
  rw [hUnits]
  exact basisTransvectionCliffordUnit_conjAct_eq_basisTransvectionLinearEquiv
    (K := K) (W := W) b t (d := z.1) (u := z.2)

/-- Every basis transvection in the Levi copy of `GL(W)` lies in the spin image. -/
theorem dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  refine ⟨basisTransvectionSpin (K := K) (W := W) b t, ?_⟩
  exact spinSpecialOrthogonalRepresentation_basisTransvectionSpin
    (K := K) (W := W) b t

/-- Transvections supported on two basis lines lie in the spin image. This form is convenient for
the four-transvection diagonal block factorization. -/
theorem dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (c : K) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord j)) (v := c • b i)
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  let t : Matrix.TransvectionStruct ι K := ⟨i, j, hij, -c⟩
  have htrans :
      LinearEquiv.transvection (f := -(b.coord j)) (v := c • b i)
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) =
        basisTransvectionLinearEquiv (K := K) (W := W) b t := by
    ext x
    simp [basisTransvectionLinearEquiv, LinearMap.transvection.apply, t,
      smul_smul, mul_comm, mul_left_comm, mul_assoc]
  rw [htrans]
  exact dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range
    (K := K) (W := W) b t

/-- Products of basis transvections lie in the spin image. -/
theorem dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (L : List (Matrix.TransvectionStruct ι K)) :
    (L.map (fun t =>
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t))).prod ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  induction L with
  | nil =>
      simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _
        (dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range
          (K := K) (W := W) b t)
        ih

/-- The canonical determinant-one two-line basis scaling block lies in the spin image. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_mem_spin_range
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹)) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rw [dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_eq_transvection_four
    (K := K) (W := W) (b := b) (i := i) (j := j) hij a]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range
          (K := K) (W := W) b hij ((1 : K) - (a : K)))
        (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range
          (K := K) (W := W) b hij.symm (-1 : K)))
      (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range
        (K := K) (W := W) b hij ((1 : K) - (a : K)⁻¹)))
    (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range
      (K := K) (W := W) b hij.symm (a : K))

/-- A square-determinant basis scaling lies in the spin image. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_mem_spin_range_of_prod_eq_sq
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) (u : Kˣ)
    (hprod : (∏ j, t j) = u ^ 2) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rw [dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
    (K := K) (W := W) (b := b) (i := i) (t := t) (u := u) hprod]
  exact Subgroup.mul_mem _
    (dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_sq_mem_range
      (K := K) (W := W) (f := b.coord i) (w := b i)
      (by simp [Module.Basis.coord_apply]) u)
    (Finset.noncommProd_induction (s := Finset.univ.erase i)
      (f := fun j =>
        dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (basisScalingLinearEquiv (K := K) (W := W) b
            (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
      (comm := by
        intro j hj k hk hjk
        exact
          (basisScalingLinearEquiv_two_update_pairwise
            (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
            (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)))
      (p := fun y =>
        y ∈ MonoidHom.range
          (spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K W)))
      (fun _ _ hx hy => Subgroup.mul_mem _ hx hy)
      (by simp)
      (fun j hj =>
        dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_mem_spin_range
          (K := K) (W := W) b (i := j) (j := i) (Finset.mem_erase.mp hj).1
          (t j)))

/-- Any Levi element with square determinant lies in the spin image. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases
      dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
        (K := K) (W := W) (b := b) (e := e) (u := u) hdet with
    ⟨L, L', t, htprod, he⟩
  rw [he]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range
        (K := K) (W := W) b L)
      (dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_mem_spin_range_of_prod_eq_sq
        (K := K) (W := W) b i t u htprod))
    (dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range
      (K := K) (W := W) b L')

/-- Every determinant-one Levi element lies in the spin image. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_one
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W)
    (hdet : LinearEquiv.det e = 1) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  simpa [hdet] using
    (dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq
      (K := K) (W := W) b i e (1 : Kˣ) (by simpa [hdet]))

/-- If every unit is a square, then every Levi element lies in the spin image. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_square_surjective
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2))
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases hsq (LinearEquiv.det e) with ⟨u, hu⟩
  exact
    dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq
      (K := K) (W := W) b i e u hu.symm

/-- Package the explicit hyperbolic transvection Clifford unit as a spin element when a common
orthogonal norm-`-1` auxiliary vector is supplied. -/
noncomputable def dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (c : Module.Dual K W × W)
    (hc : QuadraticForm.dualProd K W c = -1)
    (hac : QuadraticMap.polar (QuadraticForm.dualProd K W) (δ, 0) c = 0)
    (hbc : QuadraticMap.polar (QuadraticForm.dualProd K W) (0, w) c = 0) :
    spinGroup (QuadraticForm.dualProd K W) :=
  ⟨(dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
      (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ),
    dualProdTransvectionCliffordUnit_mem_spinGroup_of_common_orthogonal_norm_neg_one
      (K := K) (W := W) δ w hδ c hc hac hbc⟩

@[simp]
theorem coe_dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (c : Module.Dual K W × W)
    (hc : QuadraticForm.dualProd K W c = -1)
    (hac : QuadraticMap.polar (QuadraticForm.dualProd K W) (δ, 0) c = 0)
    (hbc : QuadraticMap.polar (QuadraticForm.dualProd K W) (0, w) c = 0) :
    ((dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
        (K := K) (W := W) δ w hδ c hc hac hbc :
      spinGroup (QuadraticForm.dualProd K W)) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ := rfl

/-- The spin element attached to the explicit hyperbolic transvection maps to the corresponding
split-special-orthogonal transvection. -/
theorem spinSpecialOrthogonalRepresentation_dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W]
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0)
    (c : Module.Dual K W × W)
    (hc : QuadraticForm.dualProd K W c = -1)
    (hac : QuadraticMap.polar (QuadraticForm.dualProd K W) (δ, 0) c = 0)
    (hbc : QuadraticMap.polar (QuadraticForm.dualProd K W) (0, w) c = 0) :
    spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W)
        (dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
          (K := K) (W := W) δ w hδ c hc hac hbc) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) := by
  let xU : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ :=
    dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ
  let s : spinGroup (QuadraticForm.dualProd K W) :=
    dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
      (K := K) (W := W) δ w hδ c hc hac hbc
  change spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W) s =
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
      (LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ))
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  apply cliffordIota_injective (Q := QuadraticForm.dualProd K W)
  have hUnits : spinGroup.toUnits s = xU := by
    ext
    rfl
  rw [coe_spinSpecialOrthogonalRepresentationFiniteDimensional]
  rw [spinIsometryRepresentation_apply, spinIsometryEquiv_apply]
  rw [spinLinearRepresentation_apply, spinLinearEquiv_ι]
  rw [hUnits]
  exact dualProdTransvectionCliffordUnit_conjAct_eq_transvection
    (K := K) (W := W) (δ := δ) (w := w) hδ (d := z.1) (u := z.2)

/-- A basis transvection Clifford unit is spin as soon as the basis has a third index different
from the source and target indices of the transvection. -/
theorem basisTransvectionCliffordUnit_mem_spinGroup_of_distinct_aux
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    {k : ι} (hki : k ≠ t.i) (hkj : k ≠ t.j) :
    (((basisTransvectionCliffordUnit (K := K) (W := W) b t :
        (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
      CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        spinGroup (QuadraticForm.dualProd K W) := by
  let c : Module.Dual K W × W := (-b.coord k, b k)
  simpa [basisTransvectionCliffordUnit, c] using
    (dualProdTransvectionCliffordUnit_mem_spinGroup_of_common_orthogonal_norm_neg_one
      (K := K) (W := W)
      (δ := -((t.c : K) • b.coord t.j)) (w := b t.i)
      (hδ := by simp [Module.Basis.coord_apply, t.hij])
      (c := c)
      (by
        change (-b.coord k) (b k) = -1
        simp [Module.Basis.coord_apply])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (-((t.c : K) • b.coord t.j), 0) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hkj, hkj.symm])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (0, b t.i) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hki, hki.symm]))

/-- Package a basis transvection Clifford unit as a spin element using a third basis index. -/
noncomputable def basisTransvectionSpinOfDistinctAux
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    {k : ι} (hki : k ≠ t.i) (hkj : k ≠ t.j) :
    spinGroup (QuadraticForm.dualProd K W) :=
  ⟨(basisTransvectionCliffordUnit (K := K) (W := W) b t :
      (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ),
    basisTransvectionCliffordUnit_mem_spinGroup_of_distinct_aux
      (K := K) (W := W) b t hki hkj⟩

@[simp]
theorem coe_basisTransvectionSpinOfDistinctAux
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    {k : ι} (hki : k ≠ t.i) (hkj : k ≠ t.j) :
    ((basisTransvectionSpinOfDistinctAux (K := K) (W := W) b t hki hkj :
      spinGroup (QuadraticForm.dualProd K W)) :
      CliffordAlgebra (QuadraticForm.dualProd K W)) =
      basisTransvectionCliffordUnit (K := K) (W := W) b t := rfl

/-- The basis-transvection spin lift maps to the corresponding split-special-orthogonal Levi
transvection. -/
theorem spinSpecialOrthogonalRepresentation_basisTransvectionSpinOfDistinctAux
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K)
    {k : ι} (hki : k ≠ t.i) (hkj : k ≠ t.j) :
    spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W)
        (basisTransvectionSpinOfDistinctAux (K := K) (W := W) b t hki hkj) =
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t) := by
  let c : Module.Dual K W × W := (-b.coord k, b k)
  simpa [basisTransvectionSpinOfDistinctAux, basisTransvectionCliffordUnit,
    basisTransvectionLinearEquiv, c] using
    (spinSpecialOrthogonalRepresentation_dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
      (K := K) (W := W)
      (δ := -((t.c : K) • b.coord t.j)) (w := b t.i)
      (hδ := by simp [Module.Basis.coord_apply, t.hij])
      (c := c)
      (by
        change (-b.coord k) (b k) = -1
        simp [Module.Basis.coord_apply])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (-((t.c : K) • b.coord t.j), 0) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hkj, hkj.symm])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (0, b t.i) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hki, hki.symm]))

/-- In a finite type with more than two elements, there is an index different from any prescribed
pair. -/
theorem exists_ne_ne_of_two_lt_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι) (i j : ι) :
    ∃ k : ι, k ≠ i ∧ k ≠ j := by
  by_contra h
  have hall : ∀ k : ι, k = i ∨ k = j := by
    intro k
    by_cases hki : k = i
    · exact Or.inl hki
    · by_cases hkj : k = j
      · exact Or.inr hkj
      · exfalso
        exact h ⟨k, hki, hkj⟩
  have hsubset : (Finset.univ : Finset ι) ⊆ {i, j} := by
    intro k hk
    rcases hall k with rfl | rfl
    · simp
    · simp
  have hle : Fintype.card ι ≤ ({i, j} : Finset ι).card := by
    simpa using Finset.card_le_card hsubset
  have hpair : ({i, j} : Finset ι).card ≤ 2 := by
    exact Finset.card_le_two
  exact (Nat.not_lt_of_ge (le_trans hle hpair)) hcard

/-- In split rank at least three, every basis transvection in the Levi copy of `GL(W)` lies in the
spin image. -/
theorem dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases exists_ne_ne_of_two_lt_card hcard t.i t.j with ⟨k, hki, hkj⟩
  refine ⟨basisTransvectionSpinOfDistinctAux (K := K) (W := W) b t hki hkj, ?_⟩
  exact spinSpecialOrthogonalRepresentation_basisTransvectionSpinOfDistinctAux
    (K := K) (W := W) b t hki hkj

/-- In split rank at least three, transvections supported on two basis lines lie in the spin
image. This form is convenient for the four-transvection diagonal block factorization. -/
theorem dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (c : K) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (LinearEquiv.transvection (f := -(b.coord j)) (v := c • b i)
          (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases exists_ne_ne_of_two_lt_card hcard i j with ⟨k, hki, hkj⟩
  let aux : Module.Dual K W × W := (-b.coord k, b k)
  refine
    ⟨dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
      (K := K) (W := W) (δ := b.coord j) (w := c • b i)
      (hδ := by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])
      (c := aux)
      (by
        change (-b.coord k) (b k) = -1
        simp [Module.Basis.coord_apply])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (b.coord j, 0) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hkj, hkj.symm])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (0, c • b i) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hki, hki.symm]),
      ?_⟩
  simpa [aux] using
    (spinSpecialOrthogonalRepresentation_dualProdTransvectionSpinOfCommonOrthogonalNormNegOne
      (K := K) (W := W) (δ := b.coord j) (w := c • b i)
      (hδ := by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij])
      (c := aux)
      (by
        change (-b.coord k) (b k) = -1
        simp [Module.Basis.coord_apply])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (b.coord j, 0) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hkj, hkj.symm])
      (by
        change
          QuadraticMap.polar (QuadraticForm.dualProd K W)
              (0, c • b i) (-b.coord k, b k) = 0
        simp [QuadraticMap.polar, QuadraticForm.dualProd, Module.Basis.coord_apply,
          hki, hki.symm]))

/-- Products of basis transvections in split rank at least three lie in the spin image. -/
theorem dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (L : List (Matrix.TransvectionStruct ι K)) :
    (L.map (fun t =>
      dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisTransvectionLinearEquiv (K := K) (W := W) b t))).prod ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  induction L with
  | nil =>
      simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _
        (dualProdSpecialOrthogonalOf_basisTransvectionLinearEquiv_mem_spin_range_of_two_lt_card
          (K := K) (W := W) hcard b t)
        ih

/-- In split rank at least three, the canonical determinant-one two-line basis scaling block lies in
the spin image. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_mem_spin_range_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b
          (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹)) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rw [dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_eq_transvection_four
    (K := K) (W := W) (b := b) (i := i) (j := j) hij a]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range_of_two_lt_card
          (K := K) (W := W) hcard b hij ((1 : K) - (a : K)))
        (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range_of_two_lt_card
          (K := K) (W := W) hcard b hij.symm (-1 : K)))
      (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range_of_two_lt_card
        (K := K) (W := W) hcard b hij ((1 : K) - (a : K)⁻¹)))
    (dualProdSpecialOrthogonalOf_basisCoordTransvection_mem_spin_range_of_two_lt_card
      (K := K) (W := W) hcard b hij.symm (a : K))

/-- A square-determinant basis scaling in split rank at least three lies in the spin image. -/
theorem dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_mem_spin_range_of_prod_eq_sq_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) (u : Kˣ)
    (hprod : (∏ j, t j) = u ^ 2) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K)
        (basisScalingLinearEquiv (K := K) (W := W) b t) ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rw [dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_eq_lineScalingLinearEquiv_mul_noncommProd_two_update_of_prod_eq_sq
    (K := K) (W := W) (b := b) (i := i) (t := t) (u := u) hprod]
  exact Subgroup.mul_mem _
    (dualProdSpecialOrthogonalOf_lineScalingLinearEquiv_sq_mem_range
      (K := K) (W := W) (f := b.coord i) (w := b i)
      (by simp [Module.Basis.coord_apply]) u)
    (Finset.noncommProd_induction (s := Finset.univ.erase i)
      (f := fun j =>
        dualProdSpecialOrthogonalOfLinearEquiv (K := K)
          (basisScalingLinearEquiv (K := K) (W := W) b
            (Function.update (Function.update (1 : ι → Kˣ) j (t j)) i (t j)⁻¹)))
      (comm := by
        intro j hj k hk hjk
        exact
          (basisScalingLinearEquiv_two_update_pairwise
            (K := K) (W := W) (b := b) (i := i) (t := t) hj hk hjk).map
            (dualProdSpecialOrthogonalOfLinearEquivHom (K := K) (W := W)))
      (p := fun y =>
        y ∈ MonoidHom.range
          (spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K W)))
      (fun _ _ hx hy => Subgroup.mul_mem _ hx hy)
      (by simp)
      (fun j hj =>
        dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_two_update_mem_spin_range_of_two_lt_card
          (K := K) (W := W) hcard b (i := j) (j := i) (Finset.mem_erase.mp hj).1
          (t j)))

/-- In split rank at least three, any Levi element with square determinant lies in the spin image. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases
      dualProdSpecialOrthogonalOfLinearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
        (K := K) (W := W) (b := b) (e := e) (u := u) hdet with
    ⟨L, L', t, htprod, he⟩
  rw [he]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range_of_two_lt_card
        (K := K) (W := W) hcard b L)
      (dualProdSpecialOrthogonalOf_basisScalingLinearEquiv_mem_spin_range_of_prod_eq_sq_of_two_lt_card
        (K := K) (W := W) hcard b i t u htprod))
    (dualProdSpecialOrthogonalOf_list_basisTransvectionLinearEquiv_prod_mem_spin_range_of_two_lt_card
      (K := K) (W := W) hcard b L')

/-- In split rank at least three, every determinant-one Levi element lies in the spin image. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_one_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W)
    (hdet : LinearEquiv.det e = 1) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  simpa [hdet] using
    (dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq_of_two_lt_card
      (K := K) (W := W) hcard b i e (1 : Kˣ) (by simpa [hdet]))

/-- If every unit is a square, then every higher-rank Levi element lies in the spin image in split
rank at least three. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_square_surjective_of_two_lt_card
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Invertible (2 : K)]
    [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2))
    (hcard : 2 < Fintype.card ι)
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) e ∈
      MonoidHom.range
        (spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W)) := by
  rcases hsq (LinearEquiv.det e) with ⟨u, hu⟩
  exact
    dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq_of_two_lt_card
      (K := K) (W := W) hcard b i e u hu.symm

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
