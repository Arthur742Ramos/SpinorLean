/-
  Ambient spin-group action on the underlying quadratic module.
-/

import Spinor.SpinRep

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
* `Spinor.cliffordIota_injective`, `Spinor.cliffordAlgebraMap_injective`,
  `Spinor.cliffordIotaRangeEquiv` — the Clifford inclusion of `M` is a linear embedding in
  characteristic not two.
* `Spinor.spinConjAlgEquiv` — Clifford conjugation by a spin element as an algebra
  automorphism.
* `Spinor.spinVectorAction`, `Spinor.spinLinearEquiv`,
  `Spinor.spinLinearRepresentation : spinGroup Q →* (M ≃ₗ[R] M)` — the transported vector
  action and its packaging as a linear representation.
* `Spinor.spinVector_preserves_quadratic`, `Spinor.spinIsometryEquiv`,
  `Spinor.spinIsometryRepresentation : spinGroup Q →* Q.IsometryEquiv Q` — each spin element
  acts as an isometry of `Q`, assembled into a homomorphism.
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

end IsometryEquiv
end QuadraticMap

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
