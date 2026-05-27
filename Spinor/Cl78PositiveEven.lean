import Spinor.Cl08RealMatrix

/-!
  Positive seven- and eight-dimensional even real Bott rows.

  This file records the positive-signature even rows obtained from the
  corresponding negative rows by Mathlib's even-Clifford sign-change
  equivalence.
-/

namespace Spinor

noncomputable section

/-- The standard positive real 7-dimensional quadratic form on
`((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl70Form :
    QuadraticForm ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  -realCl07Form

@[simp] theorem realCl70Form_apply (a b c d e f g : ℝ) :
    realCl70Form ((((((a, b), c), d), e), f), g) =
      a * a + b * b + c * c + d * d + e * e + f * f + g * g := by
  simp [realCl70Form, realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(7,0)` is isomorphic to `Mat₈(ℝ)`. -/
noncomputable def realEvenCl70EquivRealMatrix8 :
    CliffordAlgebra.even realCl70Form ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl70Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl07Form)).symm.trans
      realEvenCl07EquivRealMatrix8)

/-- The standard positive real 8-dimensional quadratic form on
`(((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ)`. -/
noncomputable abbrev realCl80Form :
    QuadraticForm ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  -realCl08Form

@[simp] theorem realCl80Form_apply (a b c d e f g h : ℝ) :
    realCl80Form (((((((a, b), c), d), e), f), g), h) =
      a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h := by
  simp [realCl80Form, realCl08Form, realCl07Form, realCl06Form, realCl05Form]
  ring

/-- The even real Clifford algebra `Cl⁺(8,0)` is isomorphic to
`Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def realEvenCl80EquivRealMatrix8Prod :
    CliffordAlgebra.even realCl80Form ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [realCl80Form] using
    ((CliffordAlgebra.evenEquivEvenNeg (Q := realCl08Form)).symm.trans
      realEvenCl08EquivRealMatrix8Prod)

namespace RealClassification

/-- Canonical quadratic form for the even algebra `Cl⁺(7,0)` in the
real-classification namespace. -/
noncomputable abbrev Q_7_0 :
    QuadraticForm ℝ ((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl70Form

/-- Canonical even real-classification entry: `Cl⁺(7,0) ≃ Mat₈(ℝ)`. -/
noncomputable def cl_7_0_even_equivMatrix8 :
    CliffordAlgebra.even Q_7_0 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_7_0] using realEvenCl70EquivRealMatrix8

/-- Canonical quadratic form for the even algebra `Cl⁺(8,0)` in the
real-classification namespace. -/
noncomputable abbrev Q_8_0 :
    QuadraticForm ℝ (((((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) :=
  realCl80Form

/-- Canonical even real-classification entry:
`Cl⁺(8,0) ≃ Mat₈(ℝ) × Mat₈(ℝ)`. -/
noncomputable def cl_8_0_even_equivMatrix8Prod :
    CliffordAlgebra.even Q_8_0 ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ := by
  simpa [Q_8_0] using realEvenCl80EquivRealMatrix8Prod

end RealClassification

end

end Spinor
