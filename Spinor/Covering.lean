import Spinor.ProdNeg
import Spinor.OddClassification
import Spinor.CliffordNorm
import Spinor.LipschitzImageNorm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

/-!
  Finite-dimensional kernel packaging for the ambient spin covering map.

  The obstruction addressed here is the step from "kernel elements commute with
  everything" to "kernel elements are scalar". This file resolves that step in
  finite-dimensional nondegenerate rank by
  passing to the canonical doubled hyperbolic presentation `Q ⊕ (-Q)`,
  where the chosen-model Clifford action is an endomorphism algebra. The same
  scalar-center theorem is reused for even elements in the kernel of the
  Lipschitz linear representation, giving a scalar-unit bridge and spinor-norm
  triviality theorem for even Lipschitz kernel elements. Combined with the graded
  determinant-parity theorem from `OrthogonalAction`, this gives scalar-kernel
  and image-descent packages whenever the odd determinant branch is not `1`. The file also
  lifts the resulting kernel statement from the ambient isometry map to the
  `SO(V,Q)`-valued factor, packages the conditional covering-map statement under
  the pair-generator closure hypothesis, and records the exact split-line
  double-cover criterion: surjectivity onto `SO(1,1)` is equivalent to
  square-surjectivity of `Kˣ`.
-/

namespace Spinor

universe uK uV

open scoped TensorProduct

variable {K : Type uK} [Field K] [Invertible (2 : K)]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

omit [Invertible (2 : K)] in
private theorem prodEquiv_comp_map_inl :
    (CliffordAlgebra.prodEquiv Q (-Q)).toAlgHom.comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl Q (-Q))) =
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
        (CliffordAlgebra.evenOdd (-Q)) := by
  apply CliffordAlgebra.hom_ext
  ext v
  simp [CliffordAlgebra.ofProd_ι_mk]

/-- In finite-dimensional nondegenerate rank, an even Clifford element commuting with every
Clifford element is scalar. -/
theorem even_eq_algebraMap_of_commute [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.even Q)
    (hcomm : ∀ b : CliffordAlgebra Q, Commute a b) :
    ∃ r : K, a = algebraMap K (CliffordAlgebra Q) r := by
  let inlQ : Q →qᵢ (Q.prod <| -Q) := QuadraticMap.Isometry.inl Q (-Q)
  let inrQ : (-Q) →qᵢ (Q.prod <| -Q) := QuadraticMap.Isometry.inr Q (-Q)
  let aLift : CliffordAlgebra (Q.prod <| -Q) := CliffordAlgebra.map inlQ a
  have hcommLift : ∀ b : CliffordAlgebra (Q.prod <| -Q), Commute aLift b := by
    intro b
    refine CliffordAlgebra.induction ?_ ?_ ?_ ?_ b
    · intro r
      change Commute aLift (algebraMap K (CliffordAlgebra (Q.prod <| -Q)) r)
      simpa [aLift] using
        (Algebra.commutes (A := CliffordAlgebra (Q.prod <| -Q)) r (CliffordAlgebra.map inlQ a)).symm
    · rintro ⟨v, w⟩
      have hleft :
          Commute aLift (CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v)) := by
        change Commute (CliffordAlgebra.map inlQ a)
          (CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v))
        simpa [Commute, map_mul] using
          congrArg (CliffordAlgebra.map inlQ) (hcomm (CliffordAlgebra.ι Q v)).eq
      have hright :
          Commute aLift (CliffordAlgebra.map inrQ (CliffordAlgebra.ι (-Q) w)) := by
        simpa [aLift, inlQ, inrQ] using
          (CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
            (f₁ := inlQ) (f₂ := inrQ) (hf := QuadraticMap.IsOrtho.inl_inr)
            (m₁ := a) (m₂ := CliffordAlgebra.ι (-Q) w) ha
            (CliffordAlgebra.ι_mem_evenOdd_one (Q := -Q) w))
      have hsplit :
          CliffordAlgebra.ι (Q.prod <| -Q) (v, w) =
            CliffordAlgebra.map inlQ (CliffordAlgebra.ι Q v) +
              CliffordAlgebra.map inrQ (CliffordAlgebra.ι (-Q) w) := by
        rw [show (v, w) = (v, 0) + (0, w) by simp]
        rw [map_add, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
        rfl
      rw [hsplit]
      exact hleft.add_right hright
    · intro x y hx hy
      exact hx.mul_right hy
    · intro x y hx hy
      exact hx.add_right hy
  let P := prodNegPresentation (K := K) (V := V) Q hQ
  rcases hyperbolicClifford_eq_algebraMap_of_commute
      (K := K) (Q := ((Q.prod <| -Q) : QuadraticForm K (V × V))) (W := P.W) P.iso
      (a := aLift) hcommLift with ⟨r, hr⟩
  let scalarRight :
      CliffordAlgebra (-Q) →ₗ[K] K :=
    ((Algebra.linearMap K (CliffordAlgebra (-Q))).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (cliffordAlgebraMap_injective (Q := -Q)))).choose
  have hscalarRight :
      scalarRight.comp (Algebra.linearMap K (CliffordAlgebra (-Q))) = LinearMap.id :=
    ((Algebra.linearMap K (CliffordAlgebra (-Q))).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (cliffordAlgebraMap_injective (Q := -Q)))).choose_spec
  have hscalarRight_apply (r : K) :
      scalarRight (algebraMap K (CliffordAlgebra (-Q)) r) = r := by
    simpa using congrArg (fun f : K →ₗ[K] K => f r) hscalarRight
  have htensor :
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
          (CliffordAlgebra.evenOdd (-Q)) a =
        algebraMap K
          (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r := by
    calc
      GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
            (CliffordAlgebra.evenOdd (-Q)) a =
          CliffordAlgebra.prodEquiv Q (-Q) (CliffordAlgebra.map inlQ a) := by
            symm
            simpa [AlgHom.comp_apply] using
              congrArg
                (fun f :
                  CliffordAlgebra Q →ₐ[K]
                    CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q) => f a)
                (prodEquiv_comp_map_inl (Q := Q))
      _ = CliffordAlgebra.prodEquiv Q (-Q)
            (algebraMap K (CliffordAlgebra (Q.prod <| -Q)) r) := by
            simpa [aLift] using congrArg (CliffordAlgebra.prodEquiv Q (-Q)) hr
      _ = algebraMap K
            (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r := by
            simp
  refine ⟨r, ?_⟩
  have hmap :
      (TensorProduct.map LinearMap.id scalarRight)
          (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd Q)
            (CliffordAlgebra.evenOdd (-Q)) a) =
        (TensorProduct.map LinearMap.id scalarRight)
          (algebraMap K
            (CliffordAlgebra.evenOdd Q ᵍ⊗[K] CliffordAlgebra.evenOdd (-Q)) r) := by
    simpa [GradedTensorProduct.algebraMap_def] using
      congrArg (TensorProduct.map LinearMap.id scalarRight) htensor
  have hmap' :
      a ⊗ₜ[K] scalarRight (1 : CliffordAlgebra (-Q)) =
        algebraMap K (CliffordAlgebra Q) r ⊗ₜ[K] scalarRight (1 : CliffordAlgebra (-Q)) := by
    simpa [TensorProduct.map_tmul] using hmap
  have hsmul :
      scalarRight (1 : CliffordAlgebra (-Q)) • a =
        scalarRight (1 : CliffordAlgebra (-Q)) • algebraMap K (CliffordAlgebra Q) r := by
    simpa [GradedTensorProduct.algebraMap_def, TensorProduct.map_tmul, TensorProduct.rid_tmul] using
      congrArg (TensorProduct.rid K (CliffordAlgebra Q)) hmap'
  have hscalarOne : scalarRight (1 : CliffordAlgebra (-Q)) = 1 := by
    simpa using hscalarRight_apply (r := 1)
  simpa [hscalarOne] using hsmul

/-- In finite-dimensional nondegenerate rank, an even element in the Lipschitz linear kernel is
a scalar unit in the Clifford algebra. -/
theorem exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_mem_even
    [FiniteDimensional K V] (hQ : Q.Nondegenerate) (x : lipschitzGroup Q)
    (hx : lipschitzLinearRepresentation (Q := Q) x = 1)
    (heven : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      CliffordAlgebra.even Q) :
    ∃ u : Kˣ,
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap K (CliffordAlgebra Q) (u : K) := by
  rcases even_eq_algebraMap_of_commute (Q := Q) hQ
      (ha := heven)
      (hcomm := commute_of_lipschitzLinearRepresentation_eq_one (Q := Q) x hx) with
    ⟨r, hr⟩
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hx_zero :
        (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 0 := by
      rw [hr, hr0]
      simp
    exact Units.ne_zero ((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) hx_zero
  exact ⟨Units.mk0 r hr_ne_zero, by simpa using hr⟩

/-- Even Lipschitz linear-kernel elements have trivial global Lipschitz spinor norm square class. -/
theorem lipschitzSpinorNormClassHom_eq_one_of_linearRepresentation_eq_one_of_mem_even
    [FiniteDimensional K V] (hQ : Q.Nondegenerate) (x : lipschitzGroup Q)
    (hx : lipschitzLinearRepresentation (Q := Q) x = 1)
    (heven : (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      CliffordAlgebra.even Q) :
    lipschitzSpinorNormClassHom Q x = 1 := by
  rcases exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_mem_even
      (Q := Q) hQ x hx heven with
    ⟨u, hu⟩
  exact lipschitzSpinorNormClassHom_eq_one_of_coe_eq_algebraMap_unit Q x u hu

/-- If the determinant of the odd Lipschitz branch is not `1`, every Lipschitz linear-kernel
element is a scalar unit in finite-dimensional nondegenerate rank. -/
theorem exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_det_ne
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1)
    (x : lipschitzGroup Q)
    (hx : lipschitzLinearRepresentation (Q := Q) x = 1) :
    ∃ u : Kˣ,
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap K (CliffordAlgebra Q) (u : K) :=
  exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_mem_even
    (Q := Q) hQ x hx
    (lipschitzLinearRepresentation_mem_even_of_eq_one_of_det_ne (Q := Q) x hx hdet)

/-- Under the determinant obstruction to odd kernel elements, the global Lipschitz spinor norm
is trivial on the linear kernel. -/
theorem lipschitzSpinorNormClassHom_eq_one_of_linearRepresentation_eq_one_of_det_ne
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1)
    (x : lipschitzGroup Q)
    (hx : lipschitzLinearRepresentation (Q := Q) x = 1) :
    lipschitzSpinorNormClassHom Q x = 1 := by
  rcases exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_det_ne
      (Q := Q) hQ hdet x hx with
    ⟨u, hu⟩
  exact lipschitzSpinorNormClassHom_eq_one_of_coe_eq_algebraMap_unit Q x u hu

/-- Determinant-obstructed Lipschitz linear kernels satisfy the scalar-kernel API. -/
theorem lipschitzLinearKernelScalarUnits_of_det_ne
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1) :
    LipschitzLinearKernelScalarUnits Q where
  exists_unit_scalar_of_linearRepresentation_eq_one x hx :=
    exists_unit_scalar_of_lipschitzLinearRepresentation_eq_one_of_det_ne
      (Q := Q) hQ hdet x hx

/-- Determinant-obstructed Lipschitz linear kernels give global kernel-triviality of the
Lipschitz-group spinor-norm hom. -/
theorem lipschitzSpinorNormClassHomTrivialOnLinearKernel_of_det_ne
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1) :
    LipschitzSpinorNormClassHomTrivialOnLinearKernel Q :=
  lipschitzSpinorNormClassHomTrivialOnLinearKernel_of_linearKernelScalarUnits Q
    (lipschitzLinearKernelScalarUnits_of_det_ne (Q := Q) hQ hdet)

/-- Under the determinant obstruction to odd kernel elements, the Lipschitz spinor norm descends
to the Lipschitz linear image. -/
theorem lipschitzLinearImageSpinorNormDescends_of_det_ne
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hdet : (-1 : Kˣ) ^ (Module.finrank K V - 1) ≠ 1) :
    LipschitzLinearImageSpinorNormDescends Q :=
  lipschitzLinearImageSpinorNormDescends_of_hom_trivialOnLinearKernel Q
    (lipschitzSpinorNormClassHomTrivialOnLinearKernel_of_det_ne (Q := Q) hQ hdet)

/-- In finite-dimensional nondegenerate rank, the ambient spin-to-isometry kernel is exactly the
scalar elements `±1`. -/
theorem spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one [FiniteDimensional K V]
    (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    spinIsometryRepresentation (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  refine spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one_of_kernel_scalars
    (Q := Q) ?_ x
  intro y hy
  exact even_eq_algebraMap_of_commute (Q := Q) hQ
    (ha := spinGroup.mem_even y.property)
    (hcomm := commute_of_spinIsometryRepresentation_eq_one (Q := Q) y hy)

/-- The factored ambient spin map into `SO(V,Q)` has the same finite-dimensional kernel
description as the ambient isometry map. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_eq_one_iff_coe_eq_one_or_neg_one
    [FiniteDimensional K V] (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q) x = 1 ↔
      (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  constructor
  · intro hx
    have hx' : spinIsometryRepresentation (Q := Q) x = 1 := by
      simpa [coe_spinSpecialOrthogonalRepresentationFiniteDimensional] using
        congrArg (fun g : Q.specialOrthogonalGroup => (g : Q.IsometryEquiv Q)) hx
    exact (spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one
      (Q := Q) hQ x).1 hx'
  · intro hx
    apply Subtype.ext
    simpa [coe_spinSpecialOrthogonalRepresentationFiniteDimensional] using
      (spinIsometryRepresentation_eq_one_iff_coe_eq_one_or_neg_one (Q := Q) hQ x).2 hx

/-- Once the canonical pair generators span `SO(V,Q)`, the factored ambient spin map is
surjective and its kernel is exactly `±1`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_covering_of_pairGeneratorClosure_eq_top
    [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (hgen : Subgroup.closure (spinSpecialOrthogonalPairGeneratorSet (Q := Q)) = ⊤) :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q)) ∧
      ∀ x : spinGroup Q,
        spinSpecialOrthogonalRepresentationFiniteDimensional (Q := Q) x = 1 ↔
          (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  constructor
  · exact spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_of_pairGeneratorClosure_eq_top
      (Q := Q) hgen
  · intro x
    exact spinSpecialOrthogonalRepresentationFiniteDimensional_eq_one_iff_coe_eq_one_or_neg_one
      (Q := Q) hQ x

/-- Over fields whose unit group is entirely squares, the ambient spin map on the split hyperbolic
line is a double cover of `SO(1,1)`: it is surjective and its kernel is exactly `±1`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_of_square_surjective
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2)) :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) ∧
      ∀ x : spinGroup (QuadraticForm.dualProd K K),
        spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K K) x = 1 ↔
          (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = 1 ∨
            (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = -1 := by
  apply spinSpecialOrthogonalRepresentationFiniteDimensional_covering_of_pairGeneratorClosure_eq_top
      (Q := QuadraticForm.dualProd K K)
  · rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    ext x
    constructor
    · intro hx
      rcases (QuadraticMap.mem_radical_iff'.mp hx) with ⟨hxQ, hxrad⟩
      have hxQ' : x.1 x.2 = 0 := by
        simpa [QuadraticForm.dualProd] using hxQ
      have hx₁ : x.1 = 0 := by
        apply LinearMap.ext
        intro w
        have htest := hxrad (0, w)
        simpa [QuadraticForm.dualProd, hxQ'] using htest
      have hx₂eval : Module.Dual.eval K K x.2 = 0 := by
        ext d
        have htest := hxrad (d, 0)
        simpa [QuadraticForm.dualProd, hxQ'] using htest
      have hx₂ : x.2 = 0 := Module.eval_apply_injective K (V := K) (by
        simpa using hx₂eval)
      ext <;> simp [hx₁, hx₂]
    · intro hx
      rw [hx]
      simp
  · exact
      spinSpecialOrthogonalPairGeneratorSet_dualProdLine_closure_eq_top_of_square_surjective
        (K := K) hsq

/-- On the split hyperbolic line, the double-cover package is available exactly over fields whose
unit group is square-surjective. The kernel statement is unconditional; square-surjectivity is
precisely the extra condition needed for surjectivity onto `SO(1,1)`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_iff_square_surjective :
    (Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) ∧
      ∀ x : spinGroup (QuadraticForm.dualProd K K),
        spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K K) x = 1 ↔
          (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = 1 ∨
            (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = -1) ↔
      Function.Surjective (powMonoidHom (α := Kˣ) 2) := by
  constructor
  · intro hcover
    exact
      (spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_iff_square_surjective
        (K := K)).1 hcover.1
  · intro hsq
    exact spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_of_square_surjective
      (K := K) hsq

section AlgebraicallyClosed

variable [IsAlgClosed K]

omit [Invertible (2 : K)] in
/-- Over an algebraically closed field, every unit is a square. -/
theorem units_square_surjective_of_isAlgClosed :
    Function.Surjective (powMonoidHom (α := Kˣ) 2) := by
  intro u
  rcases IsAlgClosed.exists_eq_mul_self (u : K) with ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hzero
    have hu0 : (u : K) = 0 := by
      rw [ha, hzero, zero_mul]
    exact u.ne_zero hu0
  refine ⟨Units.mk0 a ha0, ?_⟩
  ext
  simpa [pow_two] using ha.symm

/-- Over an algebraically closed field, the split-line spin map is surjective onto `SO(1,1)`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_of_isAlgClosed :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) :=
  spinSpecialOrthogonalRepresentationFiniteDimensional_surjective_dualProdLine_of_square_surjective
    (K := K) (units_square_surjective_of_isAlgClosed (K := K))

/-- Over an algebraically closed field, the split hyperbolic line carries the full double-cover
package: surjectivity onto `SO(1,1)` and kernel `{±1}`. -/
theorem spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_of_isAlgClosed :
    Function.Surjective (spinSpecialOrthogonalRepresentationFiniteDimensional
      (Q := QuadraticForm.dualProd K K)) ∧
      ∀ x : spinGroup (QuadraticForm.dualProd K K),
        spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K K) x = 1 ↔
          (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = 1 ∨
            (x : CliffordAlgebra (QuadraticForm.dualProd K K)) = -1 :=
  spinSpecialOrthogonalRepresentationFiniteDimensional_covering_dualProdLine_of_square_surjective
    (K := K) (units_square_surjective_of_isAlgClosed (K := K))

/-- Over an algebraically closed field, every finite-basis Levi automorphism admits an explicit
even unitary Clifford lift whose split action is a normalized exterior action. -/
theorem exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_isAlgClosed
    [FiniteDimensional K V] {W : Submodule K V} [FiniteDimensional K W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) :
    ∃ (u : Kˣ) (x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ),
      LinearEquiv.det e = u ^ 2 ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (-(1 / (u : K) : K)) •
          (ExteriorAlgebra.map ((e : W →ₗ[K] W))).toLinearMap :=
  exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_square_surjective
    (K := K) (V := V) (hsq := units_square_surjective_of_isAlgClosed (K := K)) b i e

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over an algebraically closed field, every finite-basis split-Levi element lies in the spin
image because every determinant is a square. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_isAlgClosed
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) :
    dualProdSpecialOrthogonalOfLinearEquiv e ∈
      (spinSpecialOrthogonalRepresentationFiniteDimensional
        (Q := QuadraticForm.dualProd K W)).range :=
  dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_square_surjective
    (K := K) (hsq := units_square_surjective_of_isAlgClosed (K := K)) b i e

end AlgebraicallyClosed

end Spinor
