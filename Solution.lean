/-
  Palomar solution surface for SpinorLean.

  The statement-level definitions are intentionally duplicated from
  `Challenge.lean` so Comparator can compare the declaration environment
  without allowing the proof development to alter the advertised meaning.
-/

import Spinor

namespace Palomar

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) [Invertible (2 : K)]

theorem cliffordIota_injective : Function.Injective (CliffordAlgebra.ι Q) := by
  intro m₁ m₂ h
  have h' : ExteriorAlgebra.ι K m₁ = ExteriorAlgebra.ι K m₂ := by
    simpa [CliffordAlgebra.equivExterior] using congrArg (CliffordAlgebra.equivExterior Q) h
  exact (ExteriorAlgebra.ι_inj K _ _).mp h'

theorem cliffordAlgebraMap_injective : Function.Injective (algebraMap K (CliffordAlgebra Q)) := by
  intro r s h
  have h' : algebraMap K (ExteriorAlgebra K V) r = algebraMap K (ExteriorAlgebra K V) s := by
    simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
      CliffordAlgebra.changeForm_algebraMap] using congrArg (CliffordAlgebra.equivExterior Q) h
  exact (ExteriorAlgebra.algebraMap_leftInverse (R := K) V).injective h'

noncomputable def cliffordIotaRangeEquiv :
    V ≃ₗ[K] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (cliffordIota_injective Q)

@[simp]
theorem cliffordIotaRangeEquiv_apply (m : V) :
    ((cliffordIotaRangeEquiv Q) m : CliffordAlgebra Q) = CliffordAlgebra.ι Q m := rfl

@[simp]
theorem cliffordIotaRangeEquiv_symm_apply (x : LinearMap.range (CliffordAlgebra.ι Q)) :
    CliffordAlgebra.ι Q ((cliffordIotaRangeEquiv Q).symm x) = x := by
  exact congrArg Subtype.val ((cliffordIotaRangeEquiv Q).apply_symm_apply x)

noncomputable def spinConjAlgEquiv (x : spinGroup Q) :
    CliffordAlgebra Q ≃ₐ[K] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv K (CliffordAlgebra Q)
    (ConjAct.toConjAct (spinGroup.toUnits x))

@[simp]
theorem spinConjAlgEquiv_apply (x : spinGroup Q) (a : CliffordAlgebra Q) :
    spinConjAlgEquiv Q x a =
      ConjAct.toConjAct (spinGroup.toUnits x) • a := rfl

noncomputable def spinRangeAction (x : spinGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) →ₗ[K] LinearMap.range (CliffordAlgebra.ι Q) where
  toFun y := by
    let z := spinConjAlgEquiv Q x y
    refine ⟨z, ?_⟩
    let m : V := Classical.choose y.property
    have hm : CliffordAlgebra.ι Q m = (y : CliffordAlgebra Q) := Classical.choose_spec y.property
    exact by
      change ConjAct.toConjAct (spinGroup.toUnits x) • (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q)
      rw [← hm]
      exact spinGroup.conjAct_smul_ι_mem_range_ι
        (Q := Q) (x := spinGroup.toUnits x) x.prop m
  map_add' y z := by
    apply Subtype.ext
    simp [spinConjAlgEquiv]
  map_smul' a y := by
    apply Subtype.ext
    simp [spinConjAlgEquiv]

@[simp]
theorem spinRangeAction_apply (x : spinGroup Q)
    (y : LinearMap.range (CliffordAlgebra.ι Q)) :
    ((spinRangeAction Q x y : LinearMap.range (CliffordAlgebra.ι Q)) : CliffordAlgebra Q) =
      spinConjAlgEquiv Q x y := rfl

noncomputable def spinVectorAction (x : spinGroup Q) : V →ₗ[K] V :=
  (cliffordIotaRangeEquiv Q).symm.toLinearMap.comp
    ((spinRangeAction Q x).comp (cliffordIotaRangeEquiv Q).toLinearMap)

@[simp]
theorem spinVectorAction_ι (x : spinGroup Q) (m : V) :
    CliffordAlgebra.ι Q (spinVectorAction Q x m) =
      ConjAct.toConjAct (spinGroup.toUnits x) • CliffordAlgebra.ι Q m := by
  simp [spinVectorAction, spinConjAlgEquiv]

noncomputable def spinLinearEquiv (x : spinGroup Q) : V ≃ₗ[K] V :=
  { spinVectorAction Q x with
    invFun := spinVectorAction Q x⁻¹
    left_inv := by
      intro m
      apply cliffordIota_injective Q
      simp [spinVectorAction_ι]
    right_inv := by
      intro m
      apply cliffordIota_injective Q
      simp [spinVectorAction_ι] }

@[simp]
theorem spinLinearEquiv_apply (x : spinGroup Q) (m : V) :
    spinLinearEquiv Q x m = spinVectorAction Q x m := rfl

@[simp]
theorem spinLinearEquiv_ι (x : spinGroup Q) (m : V) :
    CliffordAlgebra.ι Q (spinLinearEquiv Q x m) =
      ConjAct.toConjAct (spinGroup.toUnits x) • CliffordAlgebra.ι Q m :=
  spinVectorAction_ι Q x m

theorem spinVector_preserves_quadratic (x : spinGroup Q) (m : V) :
    Q (spinLinearEquiv Q x m) = Q m := by
  have hsquare :
      CliffordAlgebra.ι Q (spinLinearEquiv Q x m) * CliffordAlgebra.ι Q (spinLinearEquiv Q x m) =
        algebraMap K (CliffordAlgebra Q) (Q m) := by
    calc
      CliffordAlgebra.ι Q (spinLinearEquiv Q x m) * CliffordAlgebra.ι Q (spinLinearEquiv Q x m) =
          spinConjAlgEquiv Q x (CliffordAlgebra.ι Q m) *
            spinConjAlgEquiv Q x (CliffordAlgebra.ι Q m) := by
              rw [spinLinearEquiv_ι Q x m]
              simp [spinConjAlgEquiv]
      _ = spinConjAlgEquiv Q x
            (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q m) := by
              symm
              exact (spinConjAlgEquiv Q x).map_mul _ _
      _ = spinConjAlgEquiv Q x (algebraMap K (CliffordAlgebra Q) (Q m)) := by
              rw [CliffordAlgebra.ι_sq_scalar (Q := Q)]
      _ = algebraMap K (CliffordAlgebra Q) (Q m) := by
              simp [spinConjAlgEquiv]
  have hsquare' :
      CliffordAlgebra.ι Q (spinLinearEquiv Q x m) * CliffordAlgebra.ι Q (spinLinearEquiv Q x m) =
        algebraMap K (CliffordAlgebra Q) (Q (spinLinearEquiv Q x m)) :=
    CliffordAlgebra.ι_sq_scalar (Q := Q) _
  apply cliffordAlgebraMap_injective Q
  exact hsquare'.symm.trans hsquare

noncomputable def spinIsometryEquiv (x : spinGroup Q) : Q.IsometryEquiv Q where
  toLinearEquiv := spinLinearEquiv Q x
  map_app' := spinVector_preserves_quadratic Q x

@[simp]
theorem spinIsometryEquiv_apply (x : spinGroup Q) (m : V) :
    spinIsometryEquiv Q x m = spinLinearEquiv Q x m := rfl

private theorem spinIsometryEquiv_eq_spinor (x : spinGroup Q) :
    spinIsometryEquiv Q x = Spinor.spinIsometryEquiv (Q := Q) x := by
  apply DFunLike.ext _ _
  intro m
  rfl

theorem splitLevi_mem_spin_isometry_range_iff_det_square
    {W : Submodule K V} [FiniteDimensional K V] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (g : W ≃ₗ[K] W) :
    QuadraticForm.dualProdIsometry (R := K) g ∈
        Set.range (spinIsometryEquiv (Q := QuadraticForm.dualProd K W)) ↔
      ∃ u : Kˣ, LinearEquiv.det g = u ^ 2 := by
  constructor
  · rintro ⟨s, hs⟩
    have hmem :
        Spinor.dualProdSpecialOrthogonalOfLinearEquiv (K := K) g ∈
          MonoidHom.range
            (Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional
              (Q := QuadraticForm.dualProd K W)) := by
      refine ⟨s, ?_⟩
      apply Subtype.ext
      simpa [Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional,
        Spinor.spinSpecialOrthogonalRepresentation,
        Spinor.spinIsometryRepresentation_apply,
        Spinor.dualProdSpecialOrthogonalOfLinearEquiv] using
        (spinIsometryEquiv_eq_spinor (Q := QuadraticForm.dualProd K W) s).symm.trans hs
    exact
      (Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_iff_exists_det_eq_sq
        (K := K) (V := V) b i g).mp hmem
  · rintro ⟨u, hu⟩
    have hmem :=
      (Spinor.dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_iff_exists_det_eq_sq
        (K := K) (V := V) b i g).mpr ⟨u, hu⟩
    rcases hmem with ⟨s, hs⟩
    have hs' :
        Spinor.spinIsometryEquiv (Q := QuadraticForm.dualProd K W) s =
          QuadraticForm.dualProdIsometry (R := K) g := by
      apply congrArg Subtype.val at hs
      simpa [Spinor.spinSpecialOrthogonalRepresentationFiniteDimensional,
        Spinor.spinSpecialOrthogonalRepresentation,
        Spinor.spinIsometryRepresentation_apply,
        Spinor.dualProdSpecialOrthogonalOfLinearEquiv] using hs
    exact ⟨s, (spinIsometryEquiv_eq_spinor (Q := QuadraticForm.dualProd K W) s).trans hs'⟩

end Palomar
