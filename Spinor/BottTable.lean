import Spinor.Cl78PositiveEven

/-!
  The theorem-facing real Bott table package.

  The concrete low-dimensional files prove each row separately. This module collects the
  already-proved split families and the first-period definite rows into one declaration whose
  type records the formalized table entries.
-/

namespace Spinor
namespace RealClassification

noncomputable section

open scoped Quaternion

local notation "H" => ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]

/-- Full real matrix algebra used in the packaged real Bott table. -/
abbrev MatR (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℝ

/-- Full complex matrix algebra, viewed as a real algebra, used in the packaged real Bott table. -/
abbrev MatC (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ

/-- Full Hamilton-quaternion matrix algebra used in the packaged real Bott table. -/
abbrev MatH (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) H

/--
The formal first-period real Bott table already proved in the component files.

The first three fields record the uniform split rows. The remaining fields record the
canonical definite rows through eight generators, together with their even Clifford
companions. This is intentionally a package of proved algebra equivalences, not a recursive
periodicity theorem for arbitrary signatures.
-/
structure PeriodEightTable where
  cl_n_n :
    (n : ℕ) → CliffordAlgebra (Q_n_n n) ≃ₐ[ℝ] MatR (2 ^ n)
  cl_n_n_even :
    (n : ℕ) → (hn : 0 < n) →
      CliffordAlgebra.even (Q_n_n n) ≃ₐ[ℝ] MatR (2 ^ (n - 1)) × MatR (2 ^ (n - 1))
  cl_succ_n_n :
    (n : ℕ) → CliffordAlgebra (Q_succ_n_n n) ≃ₐ[ℝ] MatR (2 ^ n) × MatR (2 ^ n)
  cl_0_0 :
    CliffordAlgebra Q_0_0 ≃ₐ[ℝ] ℝ
  cl_1_0 :
    CliffordAlgebra Q_1_0 ≃ₐ[ℝ] ℝ × ℝ
  cl_1_0_even :
    CliffordAlgebra.even Q_1_0 ≃ₐ[ℝ] ℝ
  cl_0_1 :
    CliffordAlgebra Q_0_1 ≃ₐ[ℝ] ℂ
  cl_0_1_even :
    CliffordAlgebra.even Q_0_1 ≃ₐ[ℝ] ℝ
  cl_0_2 :
    CliffordAlgebra Q_0_2 ≃ₐ[ℝ] H
  cl_0_2_even :
    CliffordAlgebra.even Q_0_2 ≃ₐ[ℝ] ℂ
  cl_2_0 :
    CliffordAlgebra Q_2_0 ≃ₐ[ℝ] MatR 2
  cl_2_0_even :
    CliffordAlgebra.even Q_2_0 ≃ₐ[ℝ] ℂ
  cl_3_0 :
    CliffordAlgebra Q_3_0 ≃ₐ[ℝ] MatC 2
  cl_3_0_even :
    CliffordAlgebra.even Q_3_0 ≃ₐ[ℝ] H
  cl_0_3 :
    CliffordAlgebra Q_0_3 ≃ₐ[ℝ] H × H
  cl_0_3_even :
    CliffordAlgebra.even Q_0_3 ≃ₐ[ℝ] H
  cl_0_4 :
    CliffordAlgebra Q_0_4 ≃ₐ[ℝ] MatH 2
  cl_0_4_even :
    CliffordAlgebra.even Q_0_4 ≃ₐ[ℝ] H × H
  cl_4_0 :
    CliffordAlgebra Q_4_0 ≃ₐ[ℝ] MatH 2
  cl_4_0_even :
    CliffordAlgebra.even Q_4_0 ≃ₐ[ℝ] H × H
  cl_0_5 :
    CliffordAlgebra Q_0_5 ≃ₐ[ℝ] MatC 4
  cl_0_5_even :
    CliffordAlgebra.even Q_0_5 ≃ₐ[ℝ] MatH 2
  cl_5_0 :
    CliffordAlgebra Q_5_0 ≃ₐ[ℝ] MatH 2 × MatH 2
  cl_5_0_even :
    CliffordAlgebra.even Q_5_0 ≃ₐ[ℝ] MatH 2
  cl_0_6 :
    CliffordAlgebra Q_0_6 ≃ₐ[ℝ] MatR 8
  cl_0_6_even :
    CliffordAlgebra.even Q_0_6 ≃ₐ[ℝ] MatC 4
  cl_6_0 :
    CliffordAlgebra Q_6_0 ≃ₐ[ℝ] MatH 4
  cl_6_0_even :
    CliffordAlgebra.even Q_6_0 ≃ₐ[ℝ] MatC 4
  cl_0_7 :
    CliffordAlgebra Q_0_7 ≃ₐ[ℝ] MatR 8 × MatR 8
  cl_0_7_even :
    CliffordAlgebra.even Q_0_7 ≃ₐ[ℝ] MatR 8
  cl_7_0 :
    CliffordAlgebra Q_7_0 ≃ₐ[ℝ] MatC 8
  cl_7_0_even :
    CliffordAlgebra.even Q_7_0 ≃ₐ[ℝ] MatR 8
  cl_0_8 :
    CliffordAlgebra Q_0_8 ≃ₐ[ℝ] MatR 16
  cl_0_8_even :
    CliffordAlgebra.even Q_0_8 ≃ₐ[ℝ] MatR 8 × MatR 8
  cl_8_0 :
    CliffordAlgebra Q_8_0 ≃ₐ[ℝ] MatR 16
  cl_8_0_even :
    CliffordAlgebra.even Q_8_0 ≃ₐ[ℝ] MatR 8 × MatR 8

/--
The collected first-period real Bott table. Every field is filled by one of the concrete
classification equivalences proved elsewhere in the library.
-/
noncomputable def periodEightTable : PeriodEightTable where
  cl_n_n := cl_n_n_equivMatrix
  cl_n_n_even := cl_n_n_even_equivProdMatrix
  cl_succ_n_n := cl_succ_n_n_equivProdMatrix
  cl_0_0 := cl_0_0_equivReal
  cl_1_0 := cl_1_0_equivRealProd
  cl_1_0_even := cl_1_0_even_equivReal
  cl_0_1 := cl_0_1_equivComplex
  cl_0_1_even := cl_0_1_even_equivReal
  cl_0_2 := cl_0_2_equivQuaternion
  cl_0_2_even := cl_0_2_even_equivComplex
  cl_2_0 := cl_2_0_equivMatrix2
  cl_2_0_even := cl_2_0_even_equivComplex
  cl_3_0 := cl_3_0_equivComplexMatrix2
  cl_3_0_even := cl_3_0_even_equivQuaternion
  cl_0_3 := cl_0_3_equivQuaternionProd
  cl_0_3_even := cl_0_3_even_equivQuaternion
  cl_0_4 := cl_0_4_equivQuaternionMatrix2
  cl_0_4_even := cl_0_4_even_equivQuaternionProd
  cl_4_0 := cl_4_0_equivQuaternionMatrix2
  cl_4_0_even := cl_4_0_even_equivQuaternionProd
  cl_0_5 := cl_0_5_equivComplexMatrix4
  cl_0_5_even := cl_0_5_even_equivQuaternionMatrix2
  cl_5_0 := cl_5_0_equivQuaternionMatrix2Prod
  cl_5_0_even := cl_5_0_even_equivQuaternionMatrix2
  cl_0_6 := cl_0_6_equivMatrix8
  cl_0_6_even := cl_0_6_even_equivComplexMatrix4
  cl_6_0 := cl_6_0_equivQuaternionMatrix4
  cl_6_0_even := cl_6_0_even_equivComplexMatrix4
  cl_0_7 := cl_0_7_equivMatrix8Prod
  cl_0_7_even := cl_0_7_even_equivMatrix8
  cl_7_0 := cl_7_0_equivComplexMatrix8
  cl_7_0_even := cl_7_0_even_equivMatrix8
  cl_0_8 := cl_0_8_equivMatrix16
  cl_0_8_even := cl_0_8_even_equivMatrix8Prod
  cl_8_0 := cl_8_0_equivMatrix16
  cl_8_0_even := cl_8_0_even_equivMatrix8Prod

end

end RealClassification
end Spinor
