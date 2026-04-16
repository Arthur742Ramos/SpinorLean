/-
  Shared conventions and lightweight abbreviations used across the project.
-/

import Spinor.Mathlib

/-!
# Project conventions and short aliases

Shared abbreviations used throughout SpinorLean. This file is deliberately lightweight: it
only fixes two notational shortcuts inside the `Spinor` namespace.

## Main declarations

* `Spinor.Cl Q` — abbreviation for `CliffordAlgebra Q`.
* `Spinor.Ext R M` — abbreviation for `ExteriorAlgebra R M`.
-/

namespace Spinor

universe uR uM

variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- A short alias for the Clifford algebra attached to `Q`. -/
abbrev Cl (Q : QuadraticForm R M) := CliffordAlgebra Q

/-- The exterior algebra on `M`. -/
abbrev Ext := ExteriorAlgebra R M

end Spinor
