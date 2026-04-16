/-
  Shared Mathlib imports for SpinorLean.

  This project sits on top of Mathlib's Clifford algebra, exterior algebra,
  and quadratic-form APIs.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Shared Mathlib imports

This file collects the Mathlib dependencies used throughout SpinorLean. It does not introduce
any declarations; downstream modules import it transitively via `Spinor.Notation`.

The selected imports cover Mathlib's Clifford algebra API
(`Mathlib.LinearAlgebra.CliffordAlgebra.Contraction`,
`Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup`), exterior algebra bases
(`Mathlib.LinearAlgebra.ExteriorAlgebra.Basis`), the bilinear/quadratic-form infrastructure
needed for totally isotropic subspaces (`Mathlib.LinearAlgebra.BilinearForm.Orthogonal`,
`Mathlib.LinearAlgebra.QuadraticForm.Dual`, `Radical`, `Signature`), the linear-algebra
projection API (`Mathlib.LinearAlgebra.Projection`), and Mathlib's simple-module API
(`Mathlib.RingTheory.SimpleModule.Basic`) used for the spinor irreducibility statements.
-/
