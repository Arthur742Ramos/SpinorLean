import Spinor.Covering
import Spinor.RealClassification

/-!
  Odd-dimensional obstruction for the untwisted Lipschitz linear kernel.

  The determinant-obstructed scalar-kernel theorem in `Spinor.Covering` is sharp for the
  current untwisted Clifford-conjugation action. In the one-dimensional positive real form,
  the single vector generator is an odd Lipschitz element in the linear kernel, but it is not
  a scalar Clifford unit. Hence the unconditional scalar-kernel API is false for this action.
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

end

end Spinor
