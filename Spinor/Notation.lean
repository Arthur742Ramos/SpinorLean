/-
  Shared conventions and lightweight abbreviations used across the project.
-/

import Spinor.Mathlib

namespace Spinor

universe uR uM

variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- A short alias for the Clifford algebra attached to `Q`. -/
abbrev Cl (Q : QuadraticForm R M) := CliffordAlgebra Q

/-- The exterior algebra on `M`. -/
abbrev Ext := ExteriorAlgebra R M

end Spinor
