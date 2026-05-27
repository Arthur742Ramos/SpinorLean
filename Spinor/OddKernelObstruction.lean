import Spinor.Covering
import Spinor.RealClassification

/-!
  Odd-dimensional obstruction for the untwisted Lipschitz linear kernel.

  The determinant-obstructed scalar-kernel theorem in `Spinor.Covering` is sharp for the
  current untwisted Clifford-conjugation action. In the one-dimensional positive real form,
  the single vector generator is an odd Lipschitz element in the linear kernel, but it is not
  a scalar Clifford unit. Its Lipschitz spinor-norm square class is also the nontrivial
  class of `-1`, so the unconditional kernel-triviality descent API, the image-level descent
  API, any pullback-compatible image-level square-class hom, and any pullback-compatible
  full-linear-target or isometry-target square-class hom are false for this action.
-/

namespace Spinor

noncomputable section

private abbrev Q10 : QuadraticForm ℝ ℝ :=
  RealClassification.Q_1_0

/-- The linear map underlying evaluation of `Cl(1,0)` at a square root of `1`. -/
private def realCl10EvalLinearMap (s : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun := fun r => r * s
  map_add' := by
    intro x y
    ring
  map_smul' := by
    intro a x
    simp [mul_left_comm, mul_comm]

private theorem realCl10EvalLinearMap_sq (s : ℝ) (hs : s * s = 1) (r : ℝ) :
    realCl10EvalLinearMap s r * realCl10EvalLinearMap s r =
      algebraMap ℝ ℝ (Q10 r) := by
  simp [realCl10EvalLinearMap, Q10, RealClassification.Q_1_0]
  rw [mul_assoc, mul_left_comm s, hs]
  ring

/-- Evaluation of `Cl(1,0)` at a square root `s` of `1`. -/
private noncomputable def realCl10Eval (s : ℝ) (hs : s * s = 1) :
    CliffordAlgebra Q10 →ₐ[ℝ] ℝ :=
  CliffordAlgebra.lift Q10
    ⟨realCl10EvalLinearMap s, realCl10EvalLinearMap_sq s hs⟩

@[simp]
private theorem realCl10Eval_ι (s : ℝ) (hs : s * s = 1) (r : ℝ) :
    realCl10Eval s hs (CliffordAlgebra.ι Q10 r) = r * s := by
  simpa [realCl10Eval, realCl10EvalLinearMap] using
    (CliffordAlgebra.lift_ι_apply (Q := Q10)
      (realCl10EvalLinearMap s) (realCl10EvalLinearMap_sq s hs) r)

@[simp]
private theorem realCl10Eval_algebraMap (s : ℝ) (hs : s * s = 1) (r : ℝ) :
    realCl10Eval s hs (algebraMap ℝ (CliffordAlgebra Q10) r) = r := by
  simp [realCl10Eval]

/-- The generator `ι(1)` in `Cl(1,0)` is not a scalar. -/
theorem realCl10_iota_one_ne_algebraMap (r : ℝ) :
    CliffordAlgebra.ι Q10 (1 : ℝ) ≠ algebraMap ℝ (CliffordAlgebra Q10) r := by
  intro h
  have hpos := congrArg (realCl10Eval (1 : ℝ) (by norm_num)) h
  have hneg := congrArg (realCl10Eval (-1 : ℝ) (by norm_num)) h
  have hpos' : (1 : ℝ) = r := by
    simpa using hpos
  have hneg' : (-1 : ℝ) = r := by
    simpa using hneg
  have hbad : (1 : ℝ) = -1 := hpos'.trans hneg'.symm
  norm_num at hbad

@[reducible]
private noncomputable def realCl10QOneInvertible : Invertible (Q10 (1 : ℝ)) :=
  invertibleOfNonzero (by norm_num [Q10, RealClassification.Q_1_0])

/-- The odd Lipschitz generator in the one-dimensional positive real form. -/
noncomputable def realCl10OddKernelLipschitz [Invertible (2 : ℝ)] :
    lipschitzGroup Q10 := by
  letI := realCl10QOneInvertible
  exact cliffordIotaLipschitz (Q := Q10) (1 : ℝ)

@[simp]
theorem realCl10OddKernelLipschitz_coe [Invertible (2 : ℝ)] :
    (((realCl10OddKernelLipschitz : lipschitzGroup Q10) :
        (CliffordAlgebra Q10)ˣ) : CliffordAlgebra Q10) =
      CliffordAlgebra.ι Q10 (1 : ℝ) := by
  letI := realCl10QOneInvertible
  change (((cliffordIotaLipschitz (Q := Q10) (1 : ℝ) : lipschitzGroup Q10) :
        (CliffordAlgebra Q10)ˣ) : CliffordAlgebra Q10) =
      CliffordAlgebra.ι Q10 (1 : ℝ)
  simp

/-- The odd `Cl(1,0)` generator lies in the Lipschitz linear kernel. -/
theorem realCl10OddKernelLipschitz_linearRepresentation_eq_one [Invertible (2 : ℝ)] :
    lipschitzLinearRepresentation (Q := Q10) realCl10OddKernelLipschitz = 1 := by
  letI := realCl10QOneInvertible
  ext r
  change
    lipschitzLinearRepresentation (Q := Q10)
        (cliffordIotaLipschitz (Q := Q10) (1 : ℝ)) r = r
  calc
    lipschitzLinearRepresentation (Q := Q10)
        (cliffordIotaLipschitz (Q := Q10) (1 : ℝ)) r =
        lipschitzLinearRepresentation (Q := Q10)
          (cliffordIotaLipschitz (Q := Q10) (1 : ℝ)) (r • (1 : ℝ)) := by
          simp
    _ = r • lipschitzLinearRepresentation (Q := Q10)
          (cliffordIotaLipschitz (Q := Q10) (1 : ℝ)) (1 : ℝ) := by
          rw [map_smul]
    _ = r := by
          rw [lipschitzLinearRepresentation_apply_cliffordIota_self]
          simp

/-- The one-dimensional odd kernel witness is not a scalar Clifford unit. -/
theorem realCl10OddKernelLipschitz_not_scalar [Invertible (2 : ℝ)] :
    ¬ ∃ u : ℝˣ,
      (((realCl10OddKernelLipschitz : lipschitzGroup Q10) :
          (CliffordAlgebra Q10)ˣ) : CliffordAlgebra Q10) =
        algebraMap ℝ (CliffordAlgebra Q10) (u : ℝ) := by
  rintro ⟨u, hu⟩
  exact realCl10_iota_one_ne_algebraMap (u : ℝ)
    (realCl10OddKernelLipschitz_coe.symm.trans hu)

/-- The square class of `-1` in `ℝˣ / (ℝˣ)^2` is nontrivial. -/
theorem real_units_neg_one_squareClass_ne_one :
    ((-1 : ℝˣ) : ℝˣ ⧸ MonoidHom.range (powMonoidHom (α := ℝˣ) 2)) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  rcases h with ⟨u, hu⟩
  have huval : ((u ^ 2 : ℝˣ) : ℝ) = (-1 : ℝ) := by
    simpa using congrArg (fun v : ℝˣ => (v : ℝ)) hu
  have hnonneg : 0 ≤ ((u : ℝ) ^ 2) := sq_nonneg (u : ℝ)
  have hneg : ¬ 0 ≤ ((u : ℝ) ^ 2) := by
    rw [show ((u : ℝ) ^ 2) = (-1 : ℝ) by simpa [pow_two] using huval]
    norm_num
  exact hneg hnonneg

private noncomputable def realCl10OneInvertibleQuadraticVector :
    InvertibleQuadraticVector Q10 :=
  ⟨1, by
    change IsUnit ((1 : ℝ) * 1)
    simp⟩

/-- The `Cl(1,0)` odd kernel witness has spinor-norm square class `[-1]`. -/
theorem realCl10OddKernelLipschitz_spinorNormClassHom_eq_neg_one [Invertible (2 : ℝ)] :
    lipschitzSpinorNormClassHom Q10 realCl10OddKernelLipschitz =
      ((-1 : ℝˣ) : ℝˣ ⧸ MonoidHom.range (powMonoidHom (α := ℝˣ) 2)) := by
  have hgen :
      realCl10OddKernelLipschitz =
        cliffordInvertibleVectorLipschitz Q10 realCl10OneInvertibleQuadraticVector := by
    apply Subtype.ext
    apply Units.ext
    change CliffordAlgebra.ι Q10 (1 : ℝ) = CliffordAlgebra.ι Q10 (1 : ℝ)
    rfl
  rw [hgen, lipschitzSpinorNormClassHom_cliffordInvertibleVectorLipschitz]
  congr 1
  apply Units.ext
  change (-(realCl10OneInvertibleQuadraticVector.2.unit : ℝˣ) : ℝ) = (-1 : ℝ)
  simp [realCl10OneInvertibleQuadraticVector]

/-- The `Cl(1,0)` odd kernel witness has nontrivial Lipschitz spinor norm. -/
theorem realCl10OddKernelLipschitz_spinorNormClassHom_ne_one [Invertible (2 : ℝ)] :
    lipschitzSpinorNormClassHom Q10 realCl10OddKernelLipschitz ≠ 1 := by
  rw [realCl10OddKernelLipschitz_spinorNormClassHom_eq_neg_one]
  exact real_units_neg_one_squareClass_ne_one

/-- Therefore the unconditional scalar-kernel API is false for the current untwisted
Lipschitz action, already over `Cl(1,0)`. -/
theorem not_lipschitzLinearKernelScalarUnits_realCl10 [Invertible (2 : ℝ)] :
    ¬ LipschitzLinearKernelScalarUnits Q10 := by
  intro hscalar
  rcases hscalar.exists_unit_scalar_of_linearRepresentation_eq_one
      realCl10OddKernelLipschitz
      realCl10OddKernelLipschitz_linearRepresentation_eq_one with
    ⟨u, hu⟩
  exact realCl10OddKernelLipschitz_not_scalar ⟨u, hu⟩

/-- Therefore the unconditional kernel-triviality descent API is false for the current
untwisted Lipschitz spinor norm, already over `Cl(1,0)`. -/
theorem not_lipschitzSpinorNormClassHomTrivialOnLinearKernel_realCl10 [Invertible (2 : ℝ)] :
    ¬ LipschitzSpinorNormClassHomTrivialOnLinearKernel Q10 := by
  intro hker
  exact realCl10OddKernelLipschitz_spinorNormClassHom_ne_one
    (hker.eq_one_of_linearRepresentation_eq_one realCl10OddKernelLipschitz
      realCl10OddKernelLipschitz_linearRepresentation_eq_one)

/-- Therefore the chosen Lipschitz square class is not lift-independent on the linear image,
already over `Cl(1,0)`. -/
theorem not_lipschitzLinearImageSpinorNormLiftIndependent_realCl10 [Invertible (2 : ℝ)] :
    ¬ LipschitzLinearImageSpinorNormLiftIndependent Q10 := by
  intro hlift
  exact not_lipschitzSpinorNormClassHomTrivialOnLinearKernel_realCl10
    ((lipschitzLinearImageSpinorNormLiftIndependent_iff_hom_trivialOnLinearKernel Q10).mp
      hlift)

/-- Therefore the explicit image-level descent package is false for the current untwisted
Lipschitz spinor norm, already over `Cl(1,0)`. -/
theorem not_lipschitzLinearImageSpinorNormDescends_realCl10 [Invertible (2 : ℝ)] :
    ¬ LipschitzLinearImageSpinorNormDescends Q10 := by
  intro hdesc
  exact not_lipschitzSpinorNormClassHomTrivialOnLinearKernel_realCl10
    ((lipschitzLinearImageSpinorNormDescends_iff_hom_trivialOnLinearKernel Q10).mp hdesc)

/-- There is no image-level square-class hom whose pullback along
`lipschitzLinearRepresentation.rangeRestrict` is the global Lipschitz-group spinor-norm hom,
already over `Cl(1,0)`. -/
theorem not_exists_lipschitzLinearImageSpinorNormClassHom_comp_rangeRestrict_realCl10
    [Invertible (2 : ℝ)] :
    ¬ ∃ ψ : lipschitzLinearImage Q10 →*
        ℝˣ ⧸ MonoidHom.range (powMonoidHom (α := ℝˣ) 2),
      ψ.comp (lipschitzLinearRepresentation (Q := Q10)).rangeRestrict =
        lipschitzSpinorNormClassHom Q10 := by
  rintro ⟨ψ, hψ⟩
  have hrange :
      (lipschitzLinearRepresentation (Q := Q10)).rangeRestrict
          realCl10OddKernelLipschitz = 1 := by
    apply Subtype.ext
    exact realCl10OddKernelLipschitz_linearRepresentation_eq_one
  have hpoint := congrArg (fun φ => φ realCl10OddKernelLipschitz) hψ
  have hnorm :
      lipschitzSpinorNormClassHom Q10 realCl10OddKernelLipschitz = 1 := by
    simpa [MonoidHom.comp_apply, hrange] using hpoint.symm
  exact realCl10OddKernelLipschitz_spinorNormClassHom_ne_one hnorm

/-- There is no square-class hom on the full linear representation target whose pullback along
`lipschitzLinearRepresentation` is the global Lipschitz-group spinor-norm hom, already over
`Cl(1,0)`. -/
theorem not_exists_lipschitzLinearTargetSpinorNormClassHom_comp_lipschitzLinearRepresentation_realCl10
    [Invertible (2 : ℝ)] :
    ¬ ∃ ψ : (ℝ ≃ₗ[ℝ] ℝ) →*
        ℝˣ ⧸ MonoidHom.range (powMonoidHom (α := ℝˣ) 2),
      ψ.comp (lipschitzLinearRepresentation (Q := Q10)) =
        lipschitzSpinorNormClassHom Q10 := by
  rintro ⟨ψ, hψ⟩
  have hlin :
      lipschitzLinearEquiv (Q := Q10) realCl10OddKernelLipschitz = 1 := by
    simpa [lipschitzLinearRepresentation_apply] using
      realCl10OddKernelLipschitz_linearRepresentation_eq_one
  have hpoint := congrArg (fun φ => φ realCl10OddKernelLipschitz) hψ
  have hnorm :
      lipschitzSpinorNormClassHom Q10 realCl10OddKernelLipschitz = 1 := by
    simpa [MonoidHom.comp_apply, lipschitzLinearRepresentation_apply, hlin] using hpoint.symm
  exact realCl10OddKernelLipschitz_spinorNormClassHom_ne_one hnorm

/-- There is no square-class hom on an isometry target whose pullback is the global
Lipschitz-group spinor-norm hom for a representation with the same underlying linear action as
`lipschitzLinearRepresentation`, already over `Cl(1,0)`. -/
theorem not_exists_lipschitzIsometryTargetSpinorNormClassHom_comp_realCl10
    [Invertible (2 : ℝ)] :
    ¬ ∃ ρ : lipschitzGroup Q10 →* Q10.IsometryEquiv Q10,
      ∃ ψ : Q10.IsometryEquiv Q10 →*
          ℝˣ ⧸ MonoidHom.range (powMonoidHom (α := ℝˣ) 2),
        (∀ x : lipschitzGroup Q10,
          ((ρ x : Q10.IsometryEquiv Q10) : ℝ ≃ₗ[ℝ] ℝ) =
            lipschitzLinearRepresentation (Q := Q10) x) ∧
        ψ.comp ρ = lipschitzSpinorNormClassHom Q10 := by
  rintro ⟨ρ, ψ, hlinear, hψ⟩
  have hρ :
      ρ realCl10OddKernelLipschitz = 1 := by
    apply QuadraticMap.IsometryEquiv.ext
    intro r
    have hlin :
        ((ρ realCl10OddKernelLipschitz : Q10.IsometryEquiv Q10) : ℝ ≃ₗ[ℝ] ℝ) =
          1 := by
      exact (hlinear realCl10OddKernelLipschitz).trans
        realCl10OddKernelLipschitz_linearRepresentation_eq_one
    exact LinearEquiv.congr_fun hlin r
  have hpoint := congrArg (fun φ => φ realCl10OddKernelLipschitz) hψ
  have hnorm :
      lipschitzSpinorNormClassHom Q10 realCl10OddKernelLipschitz = 1 := by
    simpa [MonoidHom.comp_apply, hρ] using hpoint.symm
  exact realCl10OddKernelLipschitz_spinorNormClassHom_ne_one hnorm

end

end Spinor
