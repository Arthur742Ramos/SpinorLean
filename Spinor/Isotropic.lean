/-
  Totally isotropic subspaces for quadratic forms.
-/

import Spinor.Notation

namespace QuadraticForm

universe uR uM

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- A submodule is totally isotropic if the quadratic form vanishes on all of its vectors. -/
def IsTotallyIsotropic (Q : QuadraticForm R M) (W : Submodule R M) : Prop :=
  ∀ x : W, Q x = 0

@[simp]
theorem isTotallyIsotropic_bot (Q : QuadraticForm R M) :
    Q.IsTotallyIsotropic (⊥ : Submodule R M) := by
  intro x
  have hx : (x : M) = 0 := by
    exact congrArg Subtype.val (Subsingleton.elim x 0)
  simp [hx]

theorem IsTotallyIsotropic.mono {Q : QuadraticForm R M} {W U : Submodule R M}
    (hU : Q.IsTotallyIsotropic U) (hWU : W ≤ U) :
    Q.IsTotallyIsotropic W := by
  intro x
  exact hU ⟨x, hWU x.property⟩

theorem isTotallyIsotropic_iff_restrict_eq_zero (Q : QuadraticForm R M) (W : Submodule R M) :
    Q.IsTotallyIsotropic W ↔ Q.restrict W = 0 := by
  constructor
  · intro hW
    ext x
    exact hW x
  · intro hW x
    simpa using DFunLike.congr_fun hW x

theorem IsTotallyIsotropic.isOrtho {Q : QuadraticForm R M} {W : Submodule R M}
    (hW : Q.IsTotallyIsotropic W) (x y : W) :
    Q.IsOrtho x y := by
  rw [QuadraticMap.isOrtho_def]
  have hxy : Q (x + y : W) = 0 := hW (x + y)
  have hx : Q x = 0 := hW x
  have hy : Q y = 0 := hW y
  simpa [hx, hy] using hxy

theorem IsTotallyIsotropic.map {Q : QuadraticForm R M} {W : Submodule R M} {M' : Type*}
    [AddCommGroup M'] [Module R M'] {Q' : QuadraticForm R M'}
    (hW : Q.IsTotallyIsotropic W) (e : Q.IsometryEquiv Q') :
    Q'.IsTotallyIsotropic (W.map e.toLinearMap) := by
  intro x
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨y, hy, rfl⟩
  exact (e.map_app y).trans (hW ⟨y, hy⟩)

/-- A totally isotropic submodule is maximal if it cannot be enlarged while staying isotropic. -/
def IsMaximalTotallyIsotropic (Q : QuadraticForm R M) (W : Submodule R M) : Prop :=
  Q.IsTotallyIsotropic W ∧
    ∀ U : Submodule R M, Q.IsTotallyIsotropic U → W ≤ U → U = W

theorem IsMaximalTotallyIsotropic.isTotallyIsotropic {Q : QuadraticForm R M} {W : Submodule R M}
    (hW : Q.IsMaximalTotallyIsotropic W) :
    Q.IsTotallyIsotropic W :=
  hW.1

theorem IsMaximalTotallyIsotropic.map {Q : QuadraticForm R M} {W : Submodule R M}
    {M' : Type*} [AddCommGroup M'] [Module R M'] {Q' : QuadraticForm R M'}
    (hW : Q.IsMaximalTotallyIsotropic W) (e : Q.IsometryEquiv Q') :
    Q'.IsMaximalTotallyIsotropic (W.map e.toLinearMap) := by
  refine ⟨hW.isTotallyIsotropic.map e, ?_⟩
  intro U hU hle
  apply le_antisymm ?_ hle
  have hU' : Q.IsTotallyIsotropic (U.map e.symm.toLinearMap) := hU.map e.symm
  have hback : W ≤ U.map e.symm.toLinearMap := by
    intro w hw
    exact ⟨e w, hle ⟨w, hw, rfl⟩, by simp⟩
  have hEq : U.map e.symm.toLinearMap = W := hW.2 _ hU' hback
  intro u hu
  have hu' : e.symm u ∈ U.map e.symm.toLinearMap := ⟨u, hu, by simp⟩
  have hw : e.symm u ∈ W := by simpa [hEq] using hu'
  exact ⟨e.symm u, hw, by simp⟩

end QuadraticForm
