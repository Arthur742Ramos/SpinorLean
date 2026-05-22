/- 
  Transport the chosen `⋀W` model along an explicit hyperbolic isometry.

  This provides the ambient Clifford and spin actions on `⋀W` whenever the quadratic form `Q`
  is presented by an explicit isometry `Q ≃ dualProd K W`. It is the split/hyperbolic transport
  layer that sits between the raw `W* × W` model and the still-open full Witt decomposition.
-/

import Spinor.ExteriorModel
import Spinor.OrthogonalAction

/-!
# Transport of the chosen `⋀W` model along an explicit hyperbolic isometry

Given an explicit hyperbolic isometry `e : Q ≃ dualProd K W`, this file transports the split
`W* × W` action on `⋀W` to an ambient `CliffordAlgebra Q`-action, restricts it to the
`spinGroup Q`, and packages the even/odd parity pieces. It is the split/hyperbolic transport
layer sitting between the raw `W* × W` model of `Spinor.ExteriorModel` and the first-class
`HyperbolicPresentation` API in `Spinor.Presentation`.

In the finite-dimensional split setting the transported Clifford action is faithful and
surjective; the resulting equivalence `CliffordAlgebra Q ≃ End(⋀W)` is packaged as
`hyperbolicCliffordEquivEnd`, and the chosen `⋀W` model is simple as a `CliffordAlgebra Q`
module. The even Clifford algebra is correspondingly packaged as
`CliffordAlgebra.even Q ≃ End(⋀^even W) × End(⋀^odd W)` via `evenHyperbolicCliffordEquivProdEnd`,
with both halves simple modules over the even Clifford algebra and (in positive split rank)
inequivalent.

## Main declarations

* `Spinor.cliffordMap_mem_evenOdd_zero`, `Spinor.cliffordMap_mem_evenOdd_one`,
  `Spinor.evenCliffordEquivOfIsometry` — Clifford-algebra transport along a quadratic-form
  isometry preserves the even/odd grading.
* `Spinor.hyperbolicCliffordAction`, `Spinor.hyperbolicModule`,
  `Spinor.hyperbolicCliffordAction_ι_sq`, `Spinor.hyperbolicCliffordAction_sq_apply` — the
  transported Clifford action and its vector relation.
* `Spinor.hyperbolicCliffordAction_injective`, `Spinor.hyperbolicCliffordAction_surjective`,
  `Spinor.hyperbolicCliffordEquivEnd` — faithfulness and the endomorphism-algebra packaging.
* `Spinor.hyperbolicCliffordAction_isSimpleModule` — the transported `⋀W` is simple.
* `Spinor.evenCliffordMap`, `Spinor.evenHyperbolicCliffordAction`,
  `Spinor.oddHyperbolicCliffordAction`, `Spinor.evenHyperbolicCliffordActionProd`,
  `Spinor.evenHyperbolicCliffordEquivProdEnd` — the even Clifford algebra and its product
  action on the chosen parity halves.
* `Spinor.evenHyperbolicCliffordAction_isSimpleModule`,
  `Spinor.oddHyperbolicCliffordAction_isSimpleModule`,
  `Spinor.not_nonempty_evenOddHyperbolicCliffordLinearEquiv` — half-spin simplicity and
  inequivalence.
* `Spinor.hyperbolicSpinRepresentation`, `Spinor.hyperbolicMulAction`,
  `Spinor.evenHyperbolicSpinRepresentation` — the restricted `spinGroup Q` representation on
  `⋀W` and on each chosen parity half.
-/

namespace Spinor

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

section GradingTransport

variable {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
variable {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K V₂}

/-- An isometric map preserves the even Clifford grading. -/
theorem cliffordMap_mem_evenOdd_zero
    (e : Q₁.IsometryEquiv Q₂)
    {a : CliffordAlgebra Q₁} (ha : a ∈ CliffordAlgebra.evenOdd Q₁ 0) :
    CliffordAlgebra.map e.toIsometry a ∈ CliffordAlgebra.evenOdd Q₂ 0 := by
  refine CliffordAlgebra.even_induction (Q := Q₁) ?_ ?_ ?_ a ha
  · intro r
    simpa using (SetLike.algebraMap_mem_graded (CliffordAlgebra.evenOdd Q₂) r)
  · intro x y hx hy ihx ihy
    simpa [map_add] using Submodule.add_mem _ ihx ihy
  · intro m₁ m₂ x hx ih
    simpa [map_mul, CliffordAlgebra.map_apply_ι, mul_assoc] using
      SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := Q₂) (e m₁) (e m₂))
        ih

/-- An isometric map preserves the odd Clifford grading. -/
theorem cliffordMap_mem_evenOdd_one
    (e : Q₁.IsometryEquiv Q₂)
    {a : CliffordAlgebra Q₁} (ha : a ∈ CliffordAlgebra.evenOdd Q₁ 1) :
    CliffordAlgebra.map e.toIsometry a ∈ CliffordAlgebra.evenOdd Q₂ 1 := by
  refine CliffordAlgebra.odd_induction (Q := Q₁) ?_ ?_ ?_ a ha
  · intro v
    simpa [CliffordAlgebra.map_apply_ι] using
      (CliffordAlgebra.ι_mem_evenOdd_one (Q := Q₂) (e v))
  · intro x y hx hy ihx ihy
    simpa [map_add] using Submodule.add_mem _ ihx ihy
  · intro m₁ m₂ x hx ih
    simpa [map_mul, CliffordAlgebra.map_apply_ι, mul_assoc] using
      SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := Q₂) (e m₁) (e m₂))
        ih

/-- Transport the even Clifford algebra along an isometry of quadratic forms. -/
noncomputable def evenCliffordEquivOfIsometry
    (e : Q₁.IsometryEquiv Q₂) :
    CliffordAlgebra.even Q₁ ≃ₐ[K] CliffordAlgebra.even Q₂ where
  toFun a := ⟨CliffordAlgebra.map e.toIsometry a.1, cliffordMap_mem_evenOdd_zero e a.2⟩
  invFun a := ⟨CliffordAlgebra.map e.symm.toIsometry a.1, cliffordMap_mem_evenOdd_zero e.symm a.2⟩
  left_inv a := by
    ext
    have hleft : e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q₁ := by
      ext v
      simp [QuadraticMap.Isometry.comp_apply, e.symm_apply_apply]
    have hmap :
        CliffordAlgebra.map e.symm.toIsometry (CliffordAlgebra.map e.toIsometry a.1) =
          CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a.1 := by
      change
        ((CliffordAlgebra.map e.symm.toIsometry).comp (CliffordAlgebra.map e.toIsometry)) a.1 =
          CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a.1
      exact congrArg (fun φ => φ a.1)
        (CliffordAlgebra.map_comp_map (f := e.symm.toIsometry) (g := e.toIsometry))
    change CliffordAlgebra.map e.symm.toIsometry (CliffordAlgebra.map e.toIsometry a.1) = a.1
    rw [hmap, hleft, CliffordAlgebra.map_id]
    rfl
  right_inv a := by
    ext
    have hright : e.toIsometry.comp e.symm.toIsometry = QuadraticMap.Isometry.id Q₂ := by
      ext v
      simp [QuadraticMap.Isometry.comp_apply, e.apply_symm_apply]
    have hmap :
        CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a.1) =
          CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a.1 := by
      change
        ((CliffordAlgebra.map e.toIsometry).comp (CliffordAlgebra.map e.symm.toIsometry)) a.1 =
          CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a.1
      exact congrArg (fun φ => φ a.1)
        (CliffordAlgebra.map_comp_map (f := e.toIsometry) (g := e.symm.toIsometry))
    change CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a.1) = a.1
    rw [hmap, hright, CliffordAlgebra.map_id]
    rfl
  map_mul' := by
    intro a b
    ext
    simp [map_mul]
  map_add' := by
    intro a b
    ext
    simp [map_add]
  commutes' := by
    intro r
    ext
    simp

end GradingTransport

section HyperbolicTransport

variable [Invertible (2 : K)]
variable {Q : QuadraticForm K V} {W : Submodule K V}

/-- Transport the split Clifford action on `⋀W` along a chosen hyperbolic isometry. -/
def hyperbolicCliffordAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra Q →ₐ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  (splitCliffordAction (K := K) W).comp (CliffordAlgebra.map e.toIsometry)

@[simp]
theorem hyperbolicCliffordAction_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra Q) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e a x =
      splitCliffordAction (K := K) W (CliffordAlgebra.map e.toIsometry a) x := by
  rfl

@[simp]
theorem hyperbolicCliffordAction_apply_ι
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) W (e v) x := by
  simp [hyperbolicCliffordAction]

/-- The transported hyperbolic action satisfies the Clifford relation on vectors. -/
@[simp]
theorem hyperbolicCliffordAction_ι_sq
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (v : V) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) *
        hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) =
      algebraMap K (Module.End K (IsotropicExteriorModel (K := K) W)) (Q v) := by
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, AlgHom.commutes]

@[simp]
theorem hyperbolicCliffordAction_sq_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (v : V)
    (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v)
        (hyperbolicCliffordAction (K := K) (W := W) e (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  simpa [hyperbolicCliffordAction_apply_ι, e.map_app v] using
    splitGeneratorAction_sq_apply (K := K) (W := W) (d := (e v).1) (w := (e v).2) (x := x)

/-- In the finite-dimensional hyperbolic case, the transported chosen-model Clifford action on `⋀W`
is faithful. -/
theorem hyperbolicCliffordAction_injective [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Injective (hyperbolicCliffordAction (K := K) (W := W) e) := by
  classical
  let b := Module.finBasis K W
  intro a a' h
  have hmap :
      CliffordAlgebra.map e.toIsometry a = CliffordAlgebra.map e.toIsometry a' := by
    apply splitCliffordAction_injective (K := K) (W := W) b
    simpa [hyperbolicCliffordAction] using h
  have hisom : e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q := by
    ext v
    exact e.symm_apply_apply v
  have hback0 := congrArg (CliffordAlgebra.map e.symm.toIsometry) hmap
  have hback :
      CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a =
        CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a' := by
    change
      ((CliffordAlgebra.map e.symm.toIsometry).comp (CliffordAlgebra.map e.toIsometry)) a =
        ((CliffordAlgebra.map e.symm.toIsometry).comp (CliffordAlgebra.map e.toIsometry)) a' at hback0
    rw [CliffordAlgebra.map_comp_map] at hback0
    exact hback0
  simpa [hisom, CliffordAlgebra.map_id] using hback

/-- The module structure on `⋀W` induced by a hyperbolic isometry `Q ≃ dualProd`. -/
abbrev hyperbolicModule (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module (CliffordAlgebra Q) (IsotropicExteriorModel (K := K) W) :=
  Module.compHom (IsotropicExteriorModel (K := K) W)
    (hyperbolicCliffordAction (K := K) (W := W) e).toRingHom

@[simp]
theorem hyperbolicClifford_smul_def (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra Q) (x : IsotropicExteriorModel (K := K) W) :
    letI := hyperbolicModule (K := K) (W := W) e
    a • x = hyperbolicCliffordAction (K := K) (W := W) e a x := rfl

/-- In the finite-dimensional hyperbolic case, the transported Clifford action on `⋀W` still hits
the full endomorphism algebra. -/
theorem hyperbolicCliffordAction_surjective [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Surjective (hyperbolicCliffordAction (K := K) (W := W) e) := by
  classical
  let b := Module.finBasis K W
  intro f
  obtain ⟨a, ha⟩ := splitCliffordAction_surjective (K := K) (W := W) b f
  refine ⟨CliffordAlgebra.map e.symm.toIsometry a, ?_⟩
  have hright :
      e.toIsometry.comp e.symm.toIsometry =
        QuadraticMap.Isometry.id (QuadraticForm.dualProd K W) := by
    ext v <;> simp [QuadraticMap.Isometry.comp_apply, e.apply_symm_apply]
  have hmap :
      CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a) =
        CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a := by
    change
      ((CliffordAlgebra.map e.toIsometry).comp (CliffordAlgebra.map e.symm.toIsometry)) a =
        CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a
    exact
      congrArg
        (fun φ : CliffordAlgebra (QuadraticForm.dualProd K W) →ₐ[K]
            CliffordAlgebra (QuadraticForm.dualProd K W) => φ a)
        (CliffordAlgebra.map_comp_map (f := e.toIsometry) (g := e.symm.toIsometry))
  change
    splitCliffordAction (K := K) W
      (CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a)) = f
  rw [hmap, hright, CliffordAlgebra.map_id]
  simpa using ha

/-- In the finite-dimensional hyperbolic case, the transported chosen-model Clifford action is an
algebra equivalence onto the full endomorphism algebra of `⋀W`. -/
noncomputable def hyperbolicCliffordEquivEnd [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  AlgEquiv.ofBijective (hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e)
    ⟨hyperbolicCliffordAction_injective (K := K) (Q := Q) (W := W) e,
      hyperbolicCliffordAction_surjective (K := K) (Q := Q) (W := W) e⟩

@[simp]
theorem hyperbolicCliffordEquivEnd_apply [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (a : CliffordAlgebra Q) :
    hyperbolicCliffordEquivEnd (K := K) (Q := Q) (W := W) e a =
      hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a :=
  rfl

/-- In the finite-dimensional hyperbolic case, any Clifford element commuting with all Clifford
elements is scalar. -/
theorem hyperbolicClifford_eq_algebraMap_of_commute [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra Q) (hcomm : ∀ b : CliffordAlgebra Q, Commute a b) :
    ∃ r : K, a = algebraMap K (CliffordAlgebra Q) r := by
  let f : Module.End K (IsotropicExteriorModel (K := K) W) :=
    hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a
  have hfcenter : f ∈ Set.center (Module.End K (IsotropicExteriorModel (K := K) W)) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨b, hb⟩ := hyperbolicCliffordAction_surjective (K := K) (Q := Q) (W := W) e g
    simpa [f, hb] using
      (congrArg (hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e) (hcomm b).eq).symm
  rcases (Module.End.mem_center_iff.mp hfcenter) with ⟨r, hr, hfscalar⟩
  refine ⟨r, ?_⟩
  apply hyperbolicCliffordAction_injective (K := K) (Q := Q) (W := W) e
  calc
    hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a = f := rfl
    _ = Module.End.smulLeft r hr := hfscalar
    _ = algebraMap K (Module.End K (IsotropicExteriorModel (K := K) W)) r := by
          ext x
          simp [Module.End.smulLeft_eq, Algebra.smul_def]
    _ = hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e
          (algebraMap K (CliffordAlgebra Q) r) := by
          symm
          exact (hyperbolicCliffordAction (K := K) (Q := Q) (W := W) e).commutes r

/-- The transported chosen-model Clifford module attached to an explicit hyperbolic presentation is
simple. -/
theorem hyperbolicCliffordAction_isSimpleModule [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    letI := hyperbolicModule (K := K) (W := W) e
    IsSimpleModule (CliffordAlgebra Q) (IsotropicExteriorModel (K := K) W) := by
  letI := hyperbolicModule (K := K) (W := W) e
  let σ : CliffordAlgebra Q →+* Module.End K (IsotropicExteriorModel (K := K) W) :=
    (hyperbolicCliffordAction (K := K) (W := W) e).toRingHom
  letI : RingHomSurjective σ := ⟨hyperbolicCliffordAction_surjective (K := K) (W := W) e⟩
  let l :
      IsotropicExteriorModel (K := K) W →ₛₗ[σ]
        IsotropicExteriorModel (K := K) W :=
    { toFun := id
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        simp [σ, hyperbolicClifford_smul_def] }
  exact
    (LinearMap.isSimpleModule_iff_of_bijective (σ := σ) (l := l)
      (by simpa [l] using Function.bijective_id)).2 inferInstance

/-- Transport the even Clifford algebra along an explicit hyperbolic isometry. -/
noncomputable def evenCliffordMap (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra.even Q →ₐ[K] CliffordAlgebra.even (QuadraticForm.dualProd K W) where
  toFun a := ⟨CliffordAlgebra.map e.toIsometry a.1,
    cliffordMap_mem_evenOdd_zero (K := K) e a.2⟩
  map_zero' := by
    ext
    simp
  map_add' := by
    intro a b
    ext
    simp [map_add]
  map_one' := by
    ext
    simp
  map_mul' := by
    intro a b
    ext
    simp [map_mul]
  commutes' := by
    intro r
    ext
    simp

omit [Invertible (2 : K)] in
/-- The transported even Clifford map is surjective. -/
theorem evenCliffordMap_surjective (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Surjective (evenCliffordMap (K := K) (Q := Q) (W := W) e) := by
  intro a
  refine ⟨⟨CliffordAlgebra.map e.symm.toIsometry a.1,
      cliffordMap_mem_evenOdd_zero (K := K) e.symm a.2⟩, ?_⟩
  ext
  have hright :
      e.toIsometry.comp e.symm.toIsometry =
        QuadraticMap.Isometry.id (QuadraticForm.dualProd K W) := by
    ext v <;> simp [QuadraticMap.Isometry.comp_apply, e.apply_symm_apply]
  have hmap :
      CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a.1) =
        CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a.1 := by
    change
      ((CliffordAlgebra.map e.toIsometry).comp (CliffordAlgebra.map e.symm.toIsometry)) a.1 =
        CliffordAlgebra.map (e.toIsometry.comp e.symm.toIsometry) a.1
    exact congrArg (fun φ => φ a.1) (CliffordAlgebra.map_comp_map (f := e.toIsometry)
      (g := e.symm.toIsometry))
  change
    CliffordAlgebra.map e.toIsometry (CliffordAlgebra.map e.symm.toIsometry a.1) = a.1
  rw [hmap, hright, CliffordAlgebra.map_id]
  rfl

omit [Invertible (2 : K)] in
/-- The transported even Clifford map is injective. -/
theorem evenCliffordMap_injective (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Injective (evenCliffordMap (K := K) (Q := Q) (W := W) e) := by
  intro a b h
  apply Subtype.ext
  have hval :
      CliffordAlgebra.map e.toIsometry a.1 = CliffordAlgebra.map e.toIsometry b.1 :=
    congrArg Subtype.val h
  have hback := congrArg (CliffordAlgebra.map e.symm.toIsometry) hval
  have hleft :
      e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q := by
    ext v
    simp [QuadraticMap.Isometry.comp_apply, e.symm_apply_apply]
  have hmapa :
      CliffordAlgebra.map e.symm.toIsometry (CliffordAlgebra.map e.toIsometry a.1) =
        CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a.1 := by
    change ((CliffordAlgebra.map e.symm.toIsometry).comp (CliffordAlgebra.map e.toIsometry)) a.1 =
      CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) a.1
    exact congrArg (fun φ => φ a.1)
      (CliffordAlgebra.map_comp_map (f := e.symm.toIsometry) (g := e.toIsometry))
  have hmapb :
      CliffordAlgebra.map e.symm.toIsometry (CliffordAlgebra.map e.toIsometry b.1) =
        CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) b.1 := by
    change ((CliffordAlgebra.map e.symm.toIsometry).comp (CliffordAlgebra.map e.toIsometry)) b.1 =
      CliffordAlgebra.map (e.symm.toIsometry.comp e.toIsometry) b.1
    exact congrArg (fun φ => φ b.1)
      (CliffordAlgebra.map_comp_map (f := e.symm.toIsometry) (g := e.toIsometry))
  rw [hmapa, hmapb, hleft, CliffordAlgebra.map_id] at hback
  exact hback

/-- The even Clifford action induced by an explicit hyperbolic presentation on the chosen even half. -/
noncomputable def evenHyperbolicCliffordAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (evenExteriorSubmodule (K := K) W) :=
  (evenSplitCliffordAction (K := K) W).comp (evenCliffordMap (K := K) (Q := Q) (W := W) e)

/-- The even Clifford action induced by an explicit hyperbolic presentation on the chosen odd half. -/
noncomputable def oddHyperbolicCliffordAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (oddExteriorSubmodule (K := K) W) :=
  (oddSplitCliffordAction (K := K) W).comp (evenCliffordMap (K := K) (Q := Q) (W := W) e)

/-- The chosen even half of `⋀W` as a module over the even Clifford algebra of `Q`. -/
noncomputable abbrev evenHyperbolicCliffordModule (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module (CliffordAlgebra.even Q) (evenExteriorSubmodule (K := K) W) :=
  Module.compHom (evenExteriorSubmodule (K := K) W)
    (evenHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e).toRingHom

/-- The chosen odd half of `⋀W` as a module over the even Clifford algebra of `Q`. -/
noncomputable abbrev oddHyperbolicCliffordModule (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module (CliffordAlgebra.even Q) (oddExteriorSubmodule (K := K) W) :=
  Module.compHom (oddExteriorSubmodule (K := K) W)
    (oddHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e).toRingHom

/-- The simultaneous even Clifford action induced by an explicit hyperbolic presentation on the two
chosen half-spin modules. -/
noncomputable def evenHyperbolicCliffordActionProd
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra.even Q →ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) W) ×
        Module.End K (oddExteriorSubmodule (K := K) W) :=
  (evenHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e).prod
    (oddHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e)

@[simp]
theorem evenHyperbolicClifford_smul_def (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra.even Q) (x : evenExteriorSubmodule (K := K) W) :
    letI := evenHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    a • x = evenHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a x := rfl

@[simp]
theorem oddHyperbolicClifford_smul_def (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (a : CliffordAlgebra.even Q) (x : oddExteriorSubmodule (K := K) W) :
    letI := oddHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    a • x = oddHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a x := rfl

/-- The simultaneous even Clifford action on the two chosen half-spin modules is surjective in the
explicit hyperbolic setting. -/
theorem evenHyperbolicCliffordActionProd_surjective [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Surjective (evenHyperbolicCliffordActionProd (K := K) (Q := Q) (W := W) e) := by
  intro f
  obtain ⟨aSplit, haSplit⟩ := evenSplitCliffordActionProd_surjective (K := K) (W := W) f
  obtain ⟨a, ha⟩ := evenCliffordMap_surjective (K := K) (Q := Q) (W := W) e aSplit
  have hEven : evenSplitCliffordAction (K := K) W aSplit = f.1 := congrArg Prod.fst haSplit
  have hOdd : oddSplitCliffordAction (K := K) W aSplit = f.2 := congrArg Prod.snd haSplit
  refine ⟨a, Prod.ext ?_ ?_⟩
  · ext x
    simpa [evenHyperbolicCliffordActionProd, evenHyperbolicCliffordAction, ha] using
      congrArg (fun g : Module.End K (evenExteriorSubmodule (K := K) W) => g x) hEven
  · ext x
    simpa [evenHyperbolicCliffordActionProd, oddHyperbolicCliffordAction, ha] using
      congrArg (fun g : Module.End K (oddExteriorSubmodule (K := K) W) => g x) hOdd

/-- The simultaneous even Clifford action on the two chosen half-spin modules is faithful in the
explicit hyperbolic setting. -/
theorem evenHyperbolicCliffordActionProd_injective [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Function.Injective (evenHyperbolicCliffordActionProd (K := K) (Q := Q) (W := W) e) := by
  intro a b h
  apply evenCliffordMap_injective (K := K) (Q := Q) (W := W) e
  apply evenSplitCliffordActionProd_injective (K := K) (W := W)
  refine Prod.ext ?_ ?_
  · simpa [evenHyperbolicCliffordAction] using congrArg Prod.fst h
  · simpa [oddHyperbolicCliffordAction] using congrArg Prod.snd h

/-- In the finite-dimensional hyperbolic case, the even Clifford algebra is identified with the
product of the endomorphism algebras of the two chosen half-spin modules. -/
noncomputable def evenHyperbolicCliffordEquivProdEnd [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K (evenExteriorSubmodule (K := K) W) ×
        Module.End K (oddExteriorSubmodule (K := K) W) :=
  AlgEquiv.ofBijective (evenHyperbolicCliffordActionProd (K := K) (Q := Q) (W := W) e)
    ⟨evenHyperbolicCliffordActionProd_injective (K := K) (Q := Q) (W := W) e,
      evenHyperbolicCliffordActionProd_surjective (K := K) (Q := Q) (W := W) e⟩

@[simp]
theorem evenHyperbolicCliffordEquivProdEnd_apply [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) (a : CliffordAlgebra.even Q) :
    evenHyperbolicCliffordEquivProdEnd (K := K) (Q := Q) (W := W) e a =
      evenHyperbolicCliffordActionProd (K := K) (Q := Q) (W := W) e a :=
  rfl

/-- The chosen even half attached to an explicit hyperbolic presentation is simple under the even
Clifford action. -/
theorem evenHyperbolicCliffordAction_isSimpleModule [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    letI := evenHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    IsSimpleModule (CliffordAlgebra.even Q) (evenExteriorSubmodule (K := K) W) := by
  letI := evenSplitCliffordModule (K := K) W
  letI := evenHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
  let σ : CliffordAlgebra.even Q →+* CliffordAlgebra.even (QuadraticForm.dualProd K W) :=
    (evenCliffordMap (K := K) (Q := Q) (W := W) e).toRingHom
  letI : RingHomSurjective σ := ⟨evenCliffordMap_surjective (K := K) (Q := Q) (W := W) e⟩
  let l :
      evenExteriorSubmodule (K := K) W →ₛₗ[σ]
        evenExteriorSubmodule (K := K) W :=
    { toFun := id
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        simp [σ, evenHyperbolicClifford_smul_def, evenHyperbolicCliffordAction,
          evenSplitClifford_smul_def] }
  exact
    (LinearMap.isSimpleModule_iff_of_bijective (σ := σ) (l := l)
      (by simpa [l] using Function.bijective_id)).2
      (evenSplitCliffordAction_isSimpleModule (K := K) (W := W))

/-- For positive split rank, the chosen odd half attached to an explicit hyperbolic presentation is
simple under the even Clifford action. -/
theorem oddHyperbolicCliffordAction_isSimpleModule [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (hW : 0 < Module.finrank K W) :
    letI := oddHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    IsSimpleModule (CliffordAlgebra.even Q) (oddExteriorSubmodule (K := K) W) := by
  letI := oddSplitCliffordModule (K := K) W
  letI := oddHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
  let σ : CliffordAlgebra.even Q →+* CliffordAlgebra.even (QuadraticForm.dualProd K W) :=
    (evenCliffordMap (K := K) (Q := Q) (W := W) e).toRingHom
  letI : RingHomSurjective σ := ⟨evenCliffordMap_surjective (K := K) (Q := Q) (W := W) e⟩
  let l :
      oddExteriorSubmodule (K := K) W →ₛₗ[σ]
        oddExteriorSubmodule (K := K) W :=
    { toFun := id
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        simp [σ, oddHyperbolicClifford_smul_def, oddHyperbolicCliffordAction,
          oddSplitClifford_smul_def] }
  exact
    (LinearMap.isSimpleModule_iff_of_bijective (σ := σ) (l := l)
      (by simpa [l] using Function.bijective_id)).2
      (oddSplitCliffordAction_isSimpleModule (K := K) (W := W) hW)

/-- Transport the split parity projector to an explicit hyperbolic presentation. -/
theorem exists_evenHyperbolicCliffordParityProjector [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    ∃ a : CliffordAlgebra.even Q,
      (∀ x : evenExteriorSubmodule (K := K) W,
        evenHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a x = x) ∧
      ∀ x : oddExteriorSubmodule (K := K) W,
        oddHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a x = 0 := by
  obtain ⟨aSplit, haEven, haOdd⟩ :=
    exists_evenSplitCliffordParityProjector (K := K) (W := W)
  obtain ⟨a, ha⟩ := evenCliffordMap_surjective (K := K) (Q := Q) (W := W) e aSplit
  refine ⟨a, ?_, ?_⟩
  · intro x
    simpa [evenHyperbolicCliffordAction, ha] using haEven x
  · intro x
    simpa [oddHyperbolicCliffordAction, ha] using haOdd x

/-- The chosen even and odd halves attached to an explicit hyperbolic presentation are inequivalent
as modules over the even Clifford algebra. -/
theorem not_nonempty_evenOddHyperbolicCliffordLinearEquiv [FiniteDimensional K V]
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    letI := evenHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    letI := oddHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
    ¬ Nonempty
      (evenExteriorSubmodule (K := K) W ≃ₗ[CliffordAlgebra.even Q]
        oddExteriorSubmodule (K := K) W) := by
  classical
  letI := evenHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
  letI := oddHyperbolicCliffordModule (K := K) (Q := Q) (W := W) e
  intro hEq
  rcases hEq with ⟨f⟩
  obtain ⟨a, haEven, haOdd⟩ :=
    exists_evenHyperbolicCliffordParityProjector (K := K) (Q := Q) (W := W) e
  let hone : evenExteriorSubmodule (K := K) W := ⟨1, by
    refine (mem_evenExteriorSubmodule_of_mem_exteriorPower (K := K) (W := W)
      (n := 0) (x := (1 : IsotropicExteriorModel (K := K) W))) ?_ (by simp)
    change (1 : IsotropicExteriorModel (K := K) W) ∈
      (LinearMap.range (ExteriorAlgebra.ι K : W →ₗ[K] IsotropicExteriorModel (K := K) W) ^ 0)
    rw [pow_zero]
    simp
  ⟩
  have hone_ne : hone ≠ 0 := by
    intro h
    have h' : (hone : IsotropicExteriorModel (K := K) W) = 0 := congrArg Subtype.val h
    exact one_ne_zero h'
  have hzero : f hone = 0 := by
    calc
      f hone = f (evenHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a hone) := by
                  rw [haEven hone]
      _ = oddHyperbolicCliffordAction (K := K) (Q := Q) (W := W) e a (f hone) := by
            simpa [evenHyperbolicClifford_smul_def, oddHyperbolicClifford_smul_def] using
              (map_smulₛₗ f a hone)
      _ = 0 := haOdd (f hone)
  have hone_eq_zero : hone = 0 := by
    exact f.injective (by simpa using hzero)
  exact hone_ne hone_eq_zero

/-- Restrict the transported hyperbolic Clifford action on `⋀W` to the spin group of `Q`. -/
def hyperbolicSpinRepresentation (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (IsotropicExteriorModel (K := K) W) :=
  (hyperbolicCliffordAction (K := K) (W := W) e).toMonoidHom.comp (SubmonoidClass.subtype (spinGroup Q))

@[simp]
theorem hyperbolicSpinRepresentation_apply
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    (g : spinGroup Q) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g =
      hyperbolicCliffordAction (K := K) (W := W) e g := rfl

/-- The spin action on `⋀W` induced by a hyperbolic isometry `Q ≃ dualProd`. -/
abbrev hyperbolicMulAction (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    MulAction (spinGroup Q) (IsotropicExteriorModel (K := K) W) :=
  MulAction.compHom (IsotropicExteriorModel (K := K) W)
    (hyperbolicSpinRepresentation (K := K) (W := W) e)

/-- The transported hyperbolic spin action preserves the chosen even summand. -/
theorem hyperbolicSpinRepresentation_mem_evenExteriorSubmodule
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {g : spinGroup Q}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g x ∈ evenExteriorSubmodule (K := K) W := by
  simpa [hyperbolicSpinRepresentation, hyperbolicCliffordAction] using
    splitCliffordAction_mem_evenExteriorSubmodule (K := K) (W := W)
      (a := CliffordAlgebra.map e.toIsometry (g : CliffordAlgebra Q))
      (cliffordMap_mem_evenOdd_zero (K := K) e (spinGroup.mem_even g.property)) hx

/-- The transported hyperbolic spin action preserves the chosen odd summand. -/
theorem hyperbolicSpinRepresentation_mem_oddExteriorSubmodule
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W))
    {g : spinGroup Q}
    {x : IsotropicExteriorModel (K := K) W} (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentation (K := K) (W := W) e g x ∈ oddExteriorSubmodule (K := K) W := by
  simpa [hyperbolicSpinRepresentation, hyperbolicCliffordAction] using
    splitCliffordAction_mem_oddExteriorSubmodule (K := K) (W := W)
      (a := CliffordAlgebra.map e.toIsometry (g : CliffordAlgebra Q))
      (cliffordMap_mem_evenOdd_zero (K := K) e (spinGroup.mem_even g.property)) hx

/-- The transported hyperbolic spin representation restricted to the chosen even summand. -/
noncomputable def evenHyperbolicSpinRepresentation
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (evenExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (hyperbolicSpinRepresentation (K := K) (W := W) e g)
      (fun x hx => hyperbolicSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := W) e hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

/-- The transported hyperbolic spin representation restricted to the chosen odd summand. -/
noncomputable def oddHyperbolicSpinRepresentation
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    spinGroup Q →* Module.End K (oddExteriorSubmodule (K := K) W) where
  toFun g :=
    LinearMap.restrict (hyperbolicSpinRepresentation (K := K) (W := W) e g)
      (fun x hx => hyperbolicSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := W) e hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

section SplitTransport

variable [FiniteDimensional K V]
variable {U : Submodule K V}

/-- Transport the chosen `⋀W` Clifford action directly from split data
`W ≤ V` plus a chosen complement `U`. -/
noncomputable def hyperbolicCliffordActionOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    CliffordAlgebra Q →ₐ[K] Module.End K (IsotropicExteriorModel (K := K) W) :=
  hyperbolicCliffordAction (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- The module structure on `⋀W` induced directly from split data `W ⊔ U = V`. -/
noncomputable abbrev hyperbolicModuleOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Module (CliffordAlgebra Q) (IsotropicExteriorModel (K := K) W) :=
  hyperbolicModule (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- Restrict the split-data Clifford action on `⋀W` to the ambient spin group. -/
noncomputable def hyperbolicSpinRepresentationOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    spinGroup Q →* Module.End K (IsotropicExteriorModel (K := K) W) :=
  hyperbolicSpinRepresentation (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- The ambient `spinGroup Q` action on `⋀W` induced directly from split data. -/
noncomputable abbrev hyperbolicMulActionOfIsCompl
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    MulAction (spinGroup Q) (IsotropicExteriorModel (K := K) W) :=
  hyperbolicMulAction (K := K) (W := W)
    (QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

@[simp]
theorem hyperbolicCliffordActionOfIsCompl_apply_ι
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU (CliffordAlgebra.ι Q v) x =
      splitGeneratorAction (K := K) W
        (QuadraticForm.splitIsometryEquivOfIsCompl
          (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU v) x := by
  exact hyperbolicCliffordAction_apply_ι
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    v x

@[simp]
theorem hyperbolicCliffordActionOfIsCompl_sq_apply
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    (v : V) (x : IsotropicExteriorModel (K := K) W) :
    hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU (CliffordAlgebra.ι Q v)
        (hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
          hQ hW hsplit hWU (CliffordAlgebra.ι Q v) x) =
      Q v • x := by
  exact hyperbolicCliffordAction_sq_apply
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    v x

/-- The split-data transported chosen-model Clifford action is faithful. -/
theorem hyperbolicCliffordActionOfIsCompl_injective
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    Function.Injective
      (hyperbolicCliffordActionOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU) := by
  exact hyperbolicCliffordAction_injective
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)

/-- The split-data ambient spin action preserves the even half of `⋀W`. -/
theorem hyperbolicSpinRepresentationOfIsCompl_mem_evenExteriorSubmodule
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    {g : spinGroup Q} {x : IsotropicExteriorModel (K := K) W}
    (hx : x ∈ evenExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentationOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
      hQ hW hsplit hWU g x ∈ evenExteriorSubmodule (K := K) W := by
  exact hyperbolicSpinRepresentation_mem_evenExteriorSubmodule
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    hx

/-- The split-data ambient spin action preserves the odd half of `⋀W`. -/
theorem hyperbolicSpinRepresentationOfIsCompl_mem_oddExteriorSubmodule
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U)
    {g : spinGroup Q} {x : IsotropicExteriorModel (K := K) W}
    (hx : x ∈ oddExteriorSubmodule (K := K) W) :
    hyperbolicSpinRepresentationOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
      hQ hW hsplit hWU g x ∈ oddExteriorSubmodule (K := K) W := by
  exact hyperbolicSpinRepresentation_mem_oddExteriorSubmodule
    (K := K) (Q := Q) (W := W)
    (e := QuadraticForm.splitIsometryEquivOfIsCompl
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU)
    hx

omit [FiniteDimensional K V] in
/-- On the split exterior model `⋀W`, any invertible Clifford element whose conjugation sends each
primal generator `(0,w)` to the Levi image of `g w` acts by a scalar multiple of the natural
exterior action of `g`, with the scalar determined by the vacuum vector. -/
theorem splitCliffordAction_eq_smul_exteriorMap_of_unit_conj_primal_eq
    {W : Submodule K V} [FiniteDimensional K W]
    (x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) (g : W ≃ₗ[K] W) (c : K)
    (hprimal : ∀ w : W,
        ConjAct.toConjAct x •
            CliffordAlgebra.ι (QuadraticForm.dualProd K W) ((0 : Module.Dual K W), w) =
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, g w))
    (h1 : splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) 1 =
        algebraMap K (IsotropicExteriorModel (K := K) W) c) :
    splitCliffordAction (K := K) W (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
      c • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let A : Module.End K (IsotropicExteriorModel (K := K) W) :=
    splitCliffordAction (K := K) W (x : CliffordAlgebra Qd)
  have hmul (a : CliffordAlgebra Qd) :
      ConjAct.toConjAct x • a * (x : CliffordAlgebra Qd) =
        (x : CliffordAlgebra Qd) * a := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    have hunit :
        (((↑(x⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
          (x : CliffordAlgebra Qd)) = 1 := by
      change (((x⁻¹) * x : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) = 1
      simp
    calc
      (x : CliffordAlgebra Qd) * a *
            ((↑(x⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
          (x : CliffordAlgebra Qd)
          = (x : CliffordAlgebra Qd) * a *
              ((((↑(x⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
                (x : CliffordAlgebra Qd))) := by
                  rw [mul_assoc]
      _ = (x : CliffordAlgebra Qd) * a * 1 := by rw [hunit]
      _ = (x : CliffordAlgebra Qd) * a := by simp
  have hsplitprimal (w : W) (y : IsotropicExteriorModel (K := K) W) :
      splitCliffordAction (K := K) W
          (CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) y =
        wedgeAction (K := K) W w y := by
    simpa [Qd, splitGeneratorAction] using
      (splitCliffordAction_apply_ι (K := K) (W := W)
        (x := ((0 : Module.Dual K W), w)) (y := y))
  have hwedge :
      ∀ w y,
        A (wedgeAction (K := K) W w y) =
          wedgeAction (K := K) W (g w) (A y) := by
    intro w y
    have hιw :
        ConjAct.toConjAct x •
            CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w) =
          CliffordAlgebra.ι Qd (0, g w) := by
      simpa [Qd] using hprimal w
    calc
      A (wedgeAction (K := K) W w y)
          = splitCliffordAction (K := K) W
              ((x : CliffordAlgebra Qd) *
                CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) y := by
                  rw [← hsplitprimal]
                  simp [A, map_mul]
      _ = splitCliffordAction (K := K) W
            (ConjAct.toConjAct x • CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w) *
              (x : CliffordAlgebra Qd)) y := by
              rw [hmul]
      _ = wedgeAction (K := K) W (g w) (A y) := by
            rw [hιw, ← hsplitprimal]
            simp [A, map_mul]
  let b := Module.finBasis K W
  exact eq_smul_exteriorMap_of_map_one_and_wedgeAction
    (K := K) (V := V) (W := W) b (g : W →ₗ[K] W) A c h1 hwedge

/-- On the split exterior model `⋀W`, any spin lift of the Levi copy of `GL(W)` acts by a scalar
multiple of the natural exterior action of the underlying linear automorphism. -/
theorem splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g) :
    ∃ c : K,
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        c • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let A : Module.End K (IsotropicExteriorModel (K := K) W) :=
    splitCliffordAction (K := K) W (s : CliffordAlgebra Qd)
  have hmul (a : CliffordAlgebra Qd) :
      spinConjAlgEquiv (Q := Qd) s a * (s : CliffordAlgebra Qd) =
        (s : CliffordAlgebra Qd) * a := by
    rw [spinConjAlgEquiv_apply, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    have hunit :
        (((↑((spinGroup.toUnits s)⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
          (s : CliffordAlgebra Qd)) = 1 := by
      change
        ((((spinGroup.toUnits s)⁻¹) * spinGroup.toUnits s : (CliffordAlgebra Qd)ˣ) :
          CliffordAlgebra Qd) = 1
      simp
    calc
      (s : CliffordAlgebra Qd) * a *
            ((↑((spinGroup.toUnits s)⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
              (s : CliffordAlgebra Qd)
          = (s : CliffordAlgebra Qd) * a *
              ((((↑((spinGroup.toUnits s)⁻¹) : (CliffordAlgebra Qd)ˣ) : CliffordAlgebra Qd) *
                (s : CliffordAlgebra Qd))) := by
                  rw [mul_assoc]
      _ = (s : CliffordAlgebra Qd) * a * 1 := by rw [hunit]
      _ = (s : CliffordAlgebra Qd) * a := by simp
  have hsplitdual (d : Module.Dual K W) (y : IsotropicExteriorModel (K := K) W) :
      splitCliffordAction (K := K) W (CliffordAlgebra.ι Qd (d, (0 : W))) y =
        contractionAction (K := K) W d y := by
    simpa [Qd, splitGeneratorAction] using
      (splitCliffordAction_apply_ι (K := K) (W := W) (x := (d, (0 : W))) (y := y))
  have hsplitprimal (w : W) (y : IsotropicExteriorModel (K := K) W) :
      splitCliffordAction (K := K) W (CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) y =
        wedgeAction (K := K) W w y := by
    simpa [Qd, splitGeneratorAction] using
      (splitCliffordAction_apply_ι (K := K) (W := W) (x := ((0 : Module.Dual K W), w)) (y := y))
  have hdual :
      ∀ d : Module.Dual K W, contractionAction (K := K) W d (A 1) = 0 := by
    intro d
    have hd_aux :
        (dualProdSpecialOrthogonalOfLinearEquiv (K := K) g).1 (g.dualMap d, (0 : W)) = (d, 0) := by
      rw [dualProdSpecialOrthogonalOfLinearEquiv_apply]
      apply Prod.ext
      · ext x
        simp
      · simp
    have hd :
        spinLinearRepresentation (Q := Qd) s (g.dualMap d, (0 : W)) = (d, 0) := by
      have h :=
        congrArg (fun e : Qd.specialOrthogonalGroup => e.1 (g.dualMap d, (0 : W))) hs
      simpa [Qd, spinLinearRepresentation_apply,
        coe_spinSpecialOrthogonalRepresentationFiniteDimensional,
        spinIsometryRepresentation_apply, spinIsometryEquiv_apply] using h.trans hd_aux
    have hιd :
        spinConjAlgEquiv (Q := Qd) s
            (CliffordAlgebra.ι Qd (g.dualMap d, (0 : W))) =
          CliffordAlgebra.ι Qd (d, (0 : W)) := by
      rw [spinConjAlgEquiv_apply,
        ← spinLinearEquiv_ι (Q := Qd) s (g.dualMap d, (0 : W)),
        ← spinLinearRepresentation_apply (Q := Qd) s, hd]
    calc
      contractionAction (K := K) W d (A 1)
          = splitCliffordAction (K := K) W
              (CliffordAlgebra.ι Qd (d, (0 : W))) (A 1) := by
                rw [hsplitdual]
      _ = splitCliffordAction (K := K) W
            (spinConjAlgEquiv (Q := Qd) s
              (CliffordAlgebra.ι Qd (g.dualMap d, (0 : W)))) (A 1) := by
              rw [hιd]
      _ = splitCliffordAction (K := K) W
            (spinConjAlgEquiv (Q := Qd) s
                (CliffordAlgebra.ι Qd (g.dualMap d, (0 : W))) *
              (s : CliffordAlgebra Qd)) 1 := by
              simp [A, map_mul]
      _ = splitCliffordAction (K := K) W
            ((s : CliffordAlgebra Qd) *
              CliffordAlgebra.ι Qd (g.dualMap d, (0 : W))) 1 := by
              rw [hmul]
      _ = A (splitCliffordAction (K := K) W
            (CliffordAlgebra.ι Qd (g.dualMap d, (0 : W))) 1) := by
              simp [A, map_mul]
      _ = 0 := by
              rw [hsplitdual]
              simpa using congrArg A
                (contractionAction_algebraMap (K := K) (W := W) (d := g.dualMap d)
                  (r := (1 : K)))
  obtain ⟨c, hc⟩ :=
    eq_algebraMap_of_forall_contractionAction_eq_zero
      (K := K) (V := V) (W := W) (x := A 1) hdual
  have hwedge :
      ∀ w x,
        A (wedgeAction (K := K) W w x) =
          wedgeAction (K := K) W (g w) (A x) := by
    intro w x
    have hw_aux :
        (dualProdSpecialOrthogonalOfLinearEquiv (K := K) g).1
          ((0 : Module.Dual K W), w) = (0, g w) := by
      rw [dualProdSpecialOrthogonalOfLinearEquiv_apply]
      simp
    have hw :
        spinLinearRepresentation (Q := Qd) s ((0 : Module.Dual K W), w) = (0, g w) := by
      have h :=
        congrArg (fun e : Qd.specialOrthogonalGroup => e.1 ((0 : Module.Dual K W), w)) hs
      simpa [Qd, spinLinearRepresentation_apply,
        coe_spinSpecialOrthogonalRepresentationFiniteDimensional,
        spinIsometryRepresentation_apply, spinIsometryEquiv_apply] using h.trans hw_aux
    have hιw :
        spinConjAlgEquiv (Q := Qd) s
            (CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) =
          CliffordAlgebra.ι Qd (0, g w) := by
      rw [spinConjAlgEquiv_apply,
        ← spinLinearEquiv_ι (Q := Qd) s ((0 : Module.Dual K W), w),
        ← spinLinearRepresentation_apply (Q := Qd) s, hw]
    calc
      A (wedgeAction (K := K) W w x)
          = splitCliffordAction (K := K) W
              ((s : CliffordAlgebra Qd) *
                CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) x := by
                  rw [← hsplitprimal]
                  simp [A, map_mul]
      _ = splitCliffordAction (K := K) W
            (spinConjAlgEquiv (Q := Qd) s
                (CliffordAlgebra.ι Qd ((0 : Module.Dual K W), w)) *
              (s : CliffordAlgebra Qd)) x := by
              rw [hmul]
      _ = wedgeAction (K := K) W (g w) (A x) := by
              rw [hιw]
              rw [← hsplitprimal]
              simp [A, map_mul]
  let b := Module.finBasis K W
  refine ⟨c, ?_⟩
  exact eq_smul_exteriorMap_of_map_one_and_wedgeAction
    (K := K) (V := V) (W := W) b (g : W →ₗ[K] W) A c hc hwedge

/-- On the split exterior model `⋀W`, any spin lift of the Levi copy of `GL(W)` acts by a
nonzero scalar multiple of the natural exterior action of the underlying linear automorphism. -/
theorem splitCliffordAction_eq_units_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g) :
    ∃ c : Kˣ,
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (c : K) • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  obtain ⟨c, hc⟩ :=
    splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
      (K := K) (V := V) s g hs
  have haction_ne_zero :
      splitCliffordAction (K := K) W (s : CliffordAlgebra Qd) ≠ 0 := by
    intro hzero
    have hinv :
        splitCliffordAction (K := K) W
              ((((spinGroup.toUnits s)⁻¹ : (CliffordAlgebra Qd)ˣ) :
                CliffordAlgebra Qd)) *
            splitCliffordAction (K := K) W (s : CliffordAlgebra Qd) =
          1 := by
      rw [← map_mul]
      change splitCliffordAction (K := K) W
          ((((spinGroup.toUnits s)⁻¹ * spinGroup.toUnits s : (CliffordAlgebra Qd)ˣ) :
            CliffordAlgebra Qd)) = 1
      simp
    have hzero_one : (0 : Module.End K (IsotropicExteriorModel (K := K) W)) = 1 := by
      simpa [hzero] using hinv
    have hzero_one_apply :
        (0 : IsotropicExteriorModel (K := K) W) = 1 :=
      congrArg (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f 1) hzero_one
    exact zero_ne_one hzero_one_apply
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply haction_ne_zero
    simpa [Qd, hc0] using hc
  exact ⟨Units.mk0 c hc_ne, by simpa [Qd] using hc⟩

/-- For a Levi spin lift, the same scalar controls the action on the bottom and top exterior
lines, and the top-line eigenvalue differs by `det g`. -/
theorem splitCliffordAction_apply_one_and_topExteriorGenerator_of
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g) :
    ∃ c : K,
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W)) 1 =
        c • (1 : IsotropicExteriorModel (K := K) W) ∧
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W)) =
        (c * ↑(LinearEquiv.det g)) •
          ExteriorAlgebra.topExteriorGenerator (K := K) (M := W) := by
  obtain ⟨c, hc⟩ :=
    splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
      (K := K) (V := V) s g hs
  refine ⟨c, ?_, ?_⟩
  · simpa using congrArg (fun f : Module.End K (IsotropicExteriorModel (K := K) W) => f 1) hc
  · calc
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))
        = c • ExteriorAlgebra.map (g : W →ₗ[K] W)
            (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W)) := by
              simpa using
                congrArg
                  (fun f : Module.End K (IsotropicExteriorModel (K := K) W) =>
                    f (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W)))
                  hc
      _ = c • (↑(LinearEquiv.det g) •
            ExteriorAlgebra.topExteriorGenerator (K := K) (M := W)) := by
              rw [ExteriorAlgebra.map_topExteriorGenerator]
      _ = (c * ↑(LinearEquiv.det g)) •
            ExteriorAlgebra.topExteriorGenerator (K := K) (M := W) := by
              simpa [Units.smul_def, smul_smul, mul_comm]

/-- Applying the basis-fixed top exterior coefficient to the previous theorem records the
determinant factor as an equality in the base field. This is a first formal invariant toward the
reverse square-determinant direction for Levi spin-image elements. -/
theorem splitCliffordAction_topExteriorCoeff_of_spinSpecialOrthogonalRepresentation_eq
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g) :
    ∃ c : K,
      splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W)) 1 =
        c • (1 : IsotropicExteriorModel (K := K) W) ∧
      ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
        (splitCliffordAction (K := K) W (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
        c * ↑(LinearEquiv.det g) := by
  obtain ⟨c, hbot, htop⟩ :=
    splitCliffordAction_apply_one_and_topExteriorGenerator_of
      (K := K) (V := V) s g hs
  refine ⟨c, hbot, ?_⟩
  rw [htop]
  simp [Units.smul_def]

/-- The spin-unitarity identity `star s * s = 1`, transported through the top exterior pairing,
normalizes the bottom/top scalar product for any Levi lift. This discharges the pairing
hypothesis used by the reverse square-determinant theorem below. -/
theorem splitCliffordAction_topExteriorCoeff_pairing_of_units_smul_exteriorMap
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W) (c : Kˣ)
    (hc :
      splitCliffordAction (K := K) W
          (s : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (c : K) • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap) :
    (c : K) *
      ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
        (splitCliffordAction (K := K) W
          (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
      1 := by
  let Qd : QuadraticForm K (Module.Dual K W × W) := QuadraticForm.dualProd K W
  let ρ := splitCliffordAction (K := K) W
  let top := ExteriorAlgebra.topExteriorGenerator (K := K) (M := W)
  have hstar_reverse :
      star (s : CliffordAlgebra Qd) =
        CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd) := by
    rw [CliffordAlgebra.star_def, spinGroup.involute_eq s.prop]
  have hreverse_mul :
      CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd) *
          (s : CliffordAlgebra Qd) =
        1 := by
    rw [← hstar_reverse]
    exact spinGroup.coe_star_mul_self s
  have hunit_action :
      ρ (CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd))
          (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W)) =
        (1 : IsotropicExteriorModel (K := K) W) := by
    calc
      ρ (CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd))
          (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W)) =
          ρ (CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd) *
              (s : CliffordAlgebra Qd)) (1 : IsotropicExteriorModel (K := K) W) := by
            simp [ρ, map_mul]
      _ = 1 := by
            rw [hreverse_mul]
            simp [ρ]
  have hpair_unit :
      ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
          (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W))
          (ρ (s : CliffordAlgebra Qd) top) =
        1 := by
    calc
      ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
          (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W))
          (ρ (s : CliffordAlgebra Qd) top) =
        ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
          (ρ (CliffordAlgebra.reverse (Q := Qd) (s : CliffordAlgebra Qd))
            (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W)))
          top := by
            simpa [ρ] using
              (topExteriorPairing_splitCliffordAction_reverse_left
                (K := K) (W := W) (a := (s : CliffordAlgebra Qd))
                (x := ρ (s : CliffordAlgebra Qd)
                  (1 : IsotropicExteriorModel (K := K) W)) (y := top)).symm
      _ = 1 := by
            rw [hunit_action]
            simp [top, ExteriorAlgebra.topExteriorPairing]
  have hbottom :
      ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W) =
        (c : K) • (1 : IsotropicExteriorModel (K := K) W) := by
    have h := congrArg
      (fun f : Module.End K (IsotropicExteriorModel (K := K) W) =>
        f (1 : IsotropicExteriorModel (K := K) W)) hc
    simpa [ρ, LinearMap.smul_apply] using h
  calc
    (c : K) *
      ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
        (splitCliffordAction (K := K) W
          (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
        ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
          ((c : K) • (1 : IsotropicExteriorModel (K := K) W))
          (ρ (s : CliffordAlgebra Qd) top) := by
          symm
          calc
            ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
                ((c : K) • (1 : IsotropicExteriorModel (K := K) W))
                (ρ (s : CliffordAlgebra Qd) top) =
              (c : K) * ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
                (1 : IsotropicExteriorModel (K := K) W) (ρ (s : CliffordAlgebra Qd) top) := by
                  simp
            _ =
              (c : K) *
                ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
                  (splitCliffordAction (K := K) W
                    (s : CliffordAlgebra (QuadraticForm.dualProd K W))
                    (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) := by
                  simp [ExteriorAlgebra.topExteriorPairing, ρ, top]
    _ = ExteriorAlgebra.topExteriorPairing (K := K) (M := W)
          (ρ (s : CliffordAlgebra Qd) (1 : IsotropicExteriorModel (K := K) W))
          (ρ (s : CliffordAlgebra Qd) top) := by
          rw [hbottom]
    _ = 1 := hpair_unit

/-- A precise reduction of the reverse square-determinant direction to the missing
top-pairing/star normalization. The hypothesis says that the scalar on the bottom exterior line
and the top coefficient of the top exterior line multiply to `1`; under that invariant, the
determinant of the Levi element is forced to be a square. -/
theorem exists_det_eq_sq_of_spinSpecialOrthogonalRepresentation_eq_of_topExteriorCoeff_pairing
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g)
    (hpair :
      ∀ c : Kˣ,
        splitCliffordAction (K := K) W
            (s : CliffordAlgebra (QuadraticForm.dualProd K W)) =
          (c : K) • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap →
        (c : K) *
          ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
            (splitCliffordAction (K := K) W
              (s : CliffordAlgebra (QuadraticForm.dualProd K W))
              (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
          1) :
    ∃ u : Kˣ, LinearEquiv.det g = u ^ 2 := by
  obtain ⟨c, hc⟩ :=
    splitCliffordAction_eq_units_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
      (K := K) (V := V) s g hs
  have htop :
      ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
        (splitCliffordAction (K := K) W
          (s : CliffordAlgebra (QuadraticForm.dualProd K W))
          (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
        (c : K) * ↑(LinearEquiv.det g) := by
    calc
      ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
          (splitCliffordAction (K := K) W
            (s : CliffordAlgebra (QuadraticForm.dualProd K W))
            (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) =
          ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
            (((c : K) • (ExteriorAlgebra.map (g : W →ₗ[K] W)).toLinearMap)
              (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) := by
            rw [hc]
      _ = (c : K) *
          ExteriorAlgebra.topExteriorCoeff (K := K) (M := W)
            (ExteriorAlgebra.map (g : W →ₗ[K] W)
              (ExteriorAlgebra.topExteriorGenerator (K := K) (M := W))) := by
            simp [LinearMap.smul_apply]
      _ = (c : K) * ↑(LinearEquiv.det g) := by
            rw [ExteriorAlgebra.topExteriorCoeff_map_topExteriorGenerator]
  have hnorm := hpair c hc
  rw [htop] at hnorm
  refine ⟨c⁻¹, ?_⟩
  apply Units.ext
  have hdet :
      ((LinearEquiv.det g : Kˣ) : K) = ((c⁻¹ ^ 2 : Kˣ) : K) := by
    have hc_ne : (c : K) ≠ 0 := c.ne_zero
    have hnorm' : (c : K) ^ 2 * ((LinearEquiv.det g : Kˣ) : K) = 1 := by
      simpa [pow_two, mul_assoc] using hnorm
    calc
      ((LinearEquiv.det g : Kˣ) : K) =
          1 / ((c : K) ^ 2) := by
            rw [eq_div_iff (pow_ne_zero 2 hc_ne)]
            simpa [mul_comm] using hnorm'
      _ = ((c⁻¹ ^ 2 : Kˣ) : K) := by
            simp [pow_two]
  exact hdet

/-- For any spin lift of a split Levi element, the Levi determinant is a square. -/
theorem exists_det_eq_sq_of_spinSpecialOrthogonalRepresentation_eq
    {W : Submodule K V} [FiniteDimensional K W]
    (s : spinGroup (QuadraticForm.dualProd K W)) (g : W ≃ₗ[K] W)
    (hs : spinSpecialOrthogonalRepresentationFiniteDimensional
          (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g) :
    ∃ u : Kˣ, LinearEquiv.det g = u ^ 2 :=
  exists_det_eq_sq_of_spinSpecialOrthogonalRepresentation_eq_of_topExteriorCoeff_pairing
    (K := K) (V := V) s g hs
    (fun c hc =>
      splitCliffordAction_topExteriorCoeff_pairing_of_units_smul_exteriorMap
        (K := K) (V := V) s g c hc)

/-- A split Levi element lies in the spin image exactly when its determinant is a square. -/
theorem dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_iff_exists_det_eq_sq
    {W : Submodule K V} [FiniteDimensional K W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (g : W ≃ₗ[K] W) :
    dualProdSpecialOrthogonalOfLinearEquiv (K := K) g ∈
        MonoidHom.range
          (spinSpecialOrthogonalRepresentationFiniteDimensional
            (Q := QuadraticForm.dualProd K W)) ↔
      ∃ u : Kˣ, LinearEquiv.det g = u ^ 2 := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    exact exists_det_eq_sq_of_spinSpecialOrthogonalRepresentation_eq
      (K := K) (V := V) (W := W) s g hs
  · rintro ⟨u, hdet⟩
    exact dualProdSpecialOrthogonalOfLinearEquiv_mem_spin_range_of_det_eq_sq
      (K := K) (W := W) b i g u hdet

omit [FiniteDimensional K V] in
/-- The explicit hyperbolic transvection Clifford unit acts exactly as the corresponding linear
transvection on the split exterior model. -/
theorem splitCliffordAction_dualProdTransvectionCliffordUnit_eq_exteriorMap_transvection
    {W : Submodule K V} [FiniteDimensional K W]
    (δ : Module.Dual K W) (w : W) (hδ : δ w = 0) :
    splitCliffordAction (K := K) W
        ((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
            (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
          CliffordAlgebra (QuadraticForm.dualProd K W)) =
      (ExteriorAlgebra.map
        ((LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)) : W →ₗ[K] W)).toLinearMap := by
  let x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ :=
    dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ
  let g : W ≃ₗ[K] W := LinearEquiv.transvection (f := -δ) (v := w) (by simpa using hδ)
  have hprimal :
      ∀ u : W,
        ConjAct.toConjAct x •
            CliffordAlgebra.ι (QuadraticForm.dualProd K W) ((0 : Module.Dual K W), u) =
          CliffordAlgebra.ι (QuadraticForm.dualProd K W) (0, g u) := by
    intro u
    simpa [x, g] using
      (dualProdTransvectionCliffordUnit_conjAct_eq_transvection
        (K := K) (W := W) (δ := δ) (w := w) hδ
        (d := (0 : Module.Dual K W)) (u := u))
  have h1 :
      splitCliffordAction (K := K) W
          ((x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W)) 1 =
        algebraMap K (IsotropicExteriorModel (K := K) W) (1 : K) := by
    rw [show ((x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) =
          ((dualProdTransvectionCliffordUnit (K := K) (W := W) δ w hδ :
            (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
              CliffordAlgebra (QuadraticForm.dualProd K W)) by rfl]
    rw [coe_dualProdTransvectionCliffordUnit]
    simp [map_add, map_mul, splitCliffordAction_apply_ι, splitGeneratorAction,
      wedgeAction_apply, contractionAction_ι, hδ]
  simpa [x, g] using
    (splitCliffordAction_eq_smul_exteriorMap_of_unit_conj_primal_eq
      (K := K) (V := V) (x := x) (g := g) (c := (1 : K)) hprimal h1)

omit [FiniteDimensional K V] in
/-- The basis-transvection Clifford unit acts exactly as the matching basis transvection on the split
exterior model. -/
theorem splitCliffordAction_basisTransvectionCliffordUnit_eq_exteriorMap
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W]
    (b : Module.Basis ι K W) (t : Matrix.TransvectionStruct ι K) :
    splitCliffordAction (K := K) W
        ((basisTransvectionCliffordUnit (K := K) (W := W) b t :
            (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
          CliffordAlgebra (QuadraticForm.dualProd K W)) =
      (ExteriorAlgebra.map
        ((basisTransvectionLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) : W →ₗ[K] W)).toLinearMap := by
  simpa [basisTransvectionLinearEquiv] using
    (splitCliffordAction_dualProdTransvectionCliffordUnit_eq_exteriorMap_transvection
      (K := K) (V := V) (W := W) (-((t.c : K) • b.coord t.j)) (b t.i)
      (by simp [Module.Basis.coord_apply, t.hij]))

omit [FiniteDimensional K V] in
/-- A product of basis-transvection Clifford units acts exactly as the natural exterior action of
the corresponding product of basis transvections. -/
theorem splitCliffordAction_list_prod_unit_eq_exteriorMap_prod_of_forall
    {α : Type*} {W : Submodule K V} [FiniteDimensional K W]
    (L : List α)
    (x : α → (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ)
    (e : α → W ≃ₗ[K] W)
    (hx : ∀ a,
      splitCliffordAction (K := K) W
          ((x a : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (ExteriorAlgebra.map ((e a : W →ₗ[K] W))).toLinearMap) :
    splitCliffordAction (K := K) W
        ((((L.map x).prod : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
          CliffordAlgebra (QuadraticForm.dualProd K W))) =
      (ExteriorAlgebra.map
        ((((L.map e).prod : W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
  induction L with
  | nil =>
      ext x
      simp [ExteriorAlgebra.map_id]
  | cons a L ih =>
      simp only [List.map_cons, List.prod_cons]
      simp only [Units.val_mul]
      rw [map_mul, hx, ih]
      let eL : W ≃ₗ[K] W := (L.map e).prod
      let ea : W ≃ₗ[K] W := e a
      change
        (ExteriorAlgebra.map (ea : W →ₗ[K] W)).toLinearMap.comp
            (ExteriorAlgebra.map (eL : W →ₗ[K] W)).toLinearMap =
          (ExteriorAlgebra.map ((eL ≪≫ₗ ea : W ≃ₗ[K] W) : W →ₗ[K] W)).toLinearMap
      apply LinearMap.ext
      intro y
      change
        (AlgHom.comp
          (ExteriorAlgebra.map (ea : W →ₗ[K] W))
          (ExteriorAlgebra.map (eL : W →ₗ[K] W))) y =
        (ExteriorAlgebra.map ((eL ≪≫ₗ ea : W ≃ₗ[K] W) : W →ₗ[K] W)) y
      rw [ExteriorAlgebra.map_comp_map]
      have hcomp :
          LinearMap.comp (ea : W →ₗ[K] W) (eL : W →ₗ[K] W) =
            ((eL ≪≫ₗ ea : W ≃ₗ[K] W) : W →ₗ[K] W) := rfl
      rw [hcomp]

omit [FiniteDimensional K V] in
/-- Multiplying two Clifford operators whose split actions are scalar multiples of exterior maps
multiplies both the scalars and the underlying linear equivalences. -/
theorem splitCliffordAction_mul_eq_smul_exteriorMap_mul_of_eq_smul_exteriorMap
    {W : Submodule K V} [FiniteDimensional K W]
    {x y : CliffordAlgebra (QuadraticForm.dualProd K W)} {c d : K}
    {e f : W ≃ₗ[K] W}
    (hx : splitCliffordAction (K := K) W x =
      c • (ExteriorAlgebra.map ((e : W →ₗ[K] W))).toLinearMap)
    (hy : splitCliffordAction (K := K) W y =
      d • (ExteriorAlgebra.map ((f : W →ₗ[K] W))).toLinearMap) :
    splitCliffordAction (K := K) W (x * y) =
      (c * d) •
        (ExteriorAlgebra.map (((e * f : W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
  ext z
  rw [map_mul, Module.End.mul_eq_comp, hx, hy]
  simpa [LinearMap.comp_apply, LinearMap.smul_apply, smul_smul, mul_comm, Function.comp_def]

omit [FiniteDimensional K V] in
/-- A product of basis-transvection Clifford units acts exactly as the natural exterior action of
the corresponding product of basis transvections. -/
theorem splitCliffordAction_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W]
    (b : Module.Basis ι K W) (L : List (Matrix.TransvectionStruct ι K)) :
    splitCliffordAction (K := K) W
        ((((L.map (basisTransvectionCliffordUnit (K := K) (W := W) b)).prod :
            (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
          CliffordAlgebra (QuadraticForm.dualProd K W))) =
      (ExteriorAlgebra.map
        ((((L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod :
            W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
  simpa using
    (splitCliffordAction_list_prod_unit_eq_exteriorMap_prod_of_forall
      (K := K) (V := V) (W := W) L
      (basisTransvectionCliffordUnit (K := K) (W := W) b)
      (basisTransvectionLinearEquiv (K := K) (W := W) b)
      (fun t => splitCliffordAction_basisTransvectionCliffordUnit_eq_exteriorMap
        (K := K) (V := V) (W := W) b t))

omit [FiniteDimensional K V] in
/-- The canonical determinant-one `2 × 2` basis scaling block admits an explicit even unitary
Clifford lift whose split action is exactly the natural exterior action of the block. -/
theorem exists_basisScalingLinearEquiv_two_updateCliffordUnit_eq_exteriorMap
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) {i j : ι} (hij : i ≠ j) (a : Kˣ) :
    ∃ x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ,
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (ExteriorAlgebra.map
          ((basisScalingLinearEquiv (K := K) (W := W) b
              (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹) :
              W ≃ₗ[K] W) : W →ₗ[K] W)).toLinearMap := by
  let t1 : Matrix.TransvectionStruct ι K := ⟨i, j, hij, (a : K) - 1⟩
  let t2 : Matrix.TransvectionStruct ι K := ⟨j, i, hij.symm, (1 : K)⟩
  let t3 : Matrix.TransvectionStruct ι K := ⟨i, j, hij, (a : K)⁻¹ - 1⟩
  let t4 : Matrix.TransvectionStruct ι K := ⟨j, i, hij.symm, -((a : K))⟩
  let L : List (Matrix.TransvectionStruct ι K) := [t1, t2, t3, t4]
  let x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ :=
    basisTransvectionCliffordUnit (K := K) (W := W) b t1 *
      basisTransvectionCliffordUnit (K := K) (W := W) b t2 *
      basisTransvectionCliffordUnit (K := K) (W := W) b t3 *
      basisTransvectionCliffordUnit (K := K) (W := W) b t4
  refine ⟨x, ?_, ?_, ?_⟩
  · change
      (((basisTransvectionCliffordUnit (K := K) (W := W) b t1 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t2 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t3 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t4 :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        unitary (CliffordAlgebra (QuadraticForm.dualProd K W))
    simpa [x, Units.val_mul, mul_assoc] using
      (Submonoid.mul_mem
        (unitary (CliffordAlgebra (QuadraticForm.dualProd K W)))
        (basisTransvectionCliffordUnit_mem_unitary (K := K) (W := W) b t1)
        (Submonoid.mul_mem
          (unitary (CliffordAlgebra (QuadraticForm.dualProd K W)))
          (basisTransvectionCliffordUnit_mem_unitary (K := K) (W := W) b t2)
          (Submonoid.mul_mem
            (unitary (CliffordAlgebra (QuadraticForm.dualProd K W)))
            (basisTransvectionCliffordUnit_mem_unitary (K := K) (W := W) b t3)
            (basisTransvectionCliffordUnit_mem_unitary (K := K) (W := W) b t4))))
  · change
      (((basisTransvectionCliffordUnit (K := K) (W := W) b t1 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t2 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t3 *
          basisTransvectionCliffordUnit (K := K) (W := W) b t4 :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        CliffordAlgebra.even (QuadraticForm.dualProd K W)
    simpa [x, Units.val_mul, mul_assoc] using
      ((CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem
        (basisTransvectionCliffordUnit_mem_even (K := K) (W := W) b t1)
        ((CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem
          (basisTransvectionCliffordUnit_mem_even (K := K) (W := W) b t2)
          ((CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem
            (basisTransvectionCliffordUnit_mem_even (K := K) (W := W) b t3)
            (basisTransvectionCliffordUnit_mem_even (K := K) (W := W) b t4))))
  · have ht1 :
        basisTransvectionLinearEquiv (K := K) (W := W) b t1 =
          LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)) • b i))
            (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) := by
      ext x
      simp [t1, basisTransvectionLinearEquiv, LinearMap.transvection.apply, sub_eq_add_neg,
        smul_smul, mul_assoc, mul_left_comm, mul_comm]
      rw [← neg_smul]
      congr 1
      ring
    have ht2 :
        basisTransvectionLinearEquiv (K := K) (W := W) b t2 =
          LinearEquiv.transvection (f := -(b.coord i)) (v := ((-1 : K) • b j))
            (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) := by
      ext x
      simp [t2, basisTransvectionLinearEquiv, LinearMap.transvection.apply, sub_eq_add_neg,
        smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have ht3 :
        basisTransvectionLinearEquiv (K := K) (W := W) b t3 =
          LinearEquiv.transvection (f := -(b.coord j)) (v := (((1 : K) - (a : K)⁻¹) • b i))
            (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) := by
      ext x
      simp [t3, basisTransvectionLinearEquiv, LinearMap.transvection.apply, sub_eq_add_neg,
        smul_smul, mul_assoc, mul_left_comm, mul_comm]
      rw [← neg_smul]
      congr 1
      ring
    have ht4 :
        basisTransvectionLinearEquiv (K := K) (W := W) b t4 =
          LinearEquiv.transvection (f := -(b.coord i)) (v := ((a : K) • b j))
            (by simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hij]) := by
      ext x
      simp [t4, basisTransvectionLinearEquiv, LinearMap.transvection.apply, sub_eq_add_neg,
        smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have hL :
        (L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod =
          basisScalingLinearEquiv (K := K) (W := W) b
            (Function.update (Function.update (fun _ => (1 : Kˣ)) i a) j a⁻¹) := by
      rw [show L = [t1, t2, t3, t4] by rfl]
      rw [basisScalingLinearEquiv_two_update_eq_transvection_four
        (K := K) (W := W) (b := b) (i := i) (j := j) hij a]
      simpa [ht1, ht2, ht3, ht4, mul_assoc]
    have hx :
        x = (L.map (basisTransvectionCliffordUnit (K := K) (W := W) b)).prod := by
      simp [x, L, mul_assoc]
    rw [hx]
    rw [splitCliffordAction_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
      (K := K) (V := V) (W := W) b L]
    simpa [hL]

omit [FiniteDimensional K V] in
/-- A list of basis-transvection Clifford units gives an explicit even unitary lift whose split
action is exactly the exterior action of the corresponding transvection product. -/
theorem exists_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (L : List (Matrix.TransvectionStruct ι K)) :
    ∃ x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ,
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (ExteriorAlgebra.map
          ((((L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod :
              W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
  refine ⟨(L.map (basisTransvectionCliffordUnit (K := K) (W := W) b)).prod, ?_, ?_, ?_⟩
  · change
      (((L.map (basisTransvectionCliffordUnit (K := K) (W := W) b)).prod :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W))
    induction L with
    | nil =>
        simp
    | cons t L ih =>
        simp only [List.map_cons, List.prod_cons, Units.val_mul]
        exact Submonoid.mul_mem _
          (basisTransvectionCliffordUnit_mem_unitary (K := K) (W := W) b t) ih
  · change
      (((L.map (basisTransvectionCliffordUnit (K := K) (W := W) b)).prod :
          (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W)
    induction L with
    | nil =>
        simp
    | cons t L ih =>
        simp only [List.map_cons, List.prod_cons, Units.val_mul]
        exact (CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem
          (basisTransvectionCliffordUnit_mem_even (K := K) (W := W) b t) ih
  · simpa using
      (splitCliffordAction_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
        (K := K) (V := V) (W := W) b L)

omit [FiniteDimensional K V] in
/-- A determinant-one basis scaling admits an explicit even unitary Clifford lift whose split
action is exactly the natural exterior action of the scaling. -/
theorem exists_basisScalingLinearEquivCliffordUnit_eq_exteriorMap_of_prod_eq_one
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ)
    (hprod : (∏ j, t j) = 1) :
    ∃ x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ,
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (ExteriorAlgebra.map
          (((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) :
              W →ₗ[K] W))).toLinearMap := by
  classical
  let s : Finset ι := Finset.univ.erase i
  let L : List ι := s.toList
  let block : ι → W ≃ₗ[K] W := fun j =>
    if hji : j = i then
      1
    else
      basisScalingLinearEquiv (K := K) (W := W) b
        (Function.update (Function.update (fun _ => (1 : Kˣ)) j (t j)) i (t j)⁻¹)
  let xj : ι → (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ := fun j =>
    if hji : j = i then
      1
    else
      Classical.choose
        (exists_basisScalingLinearEquiv_two_updateCliffordUnit_eq_exteriorMap
          (K := K) (V := V) (W := W) b (i := j) (j := i) hji (a := t j))
  have hxj :
      ∀ j,
        splitCliffordAction (K := K) W
            ((xj j : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
              CliffordAlgebra (QuadraticForm.dualProd K W)) =
          (ExteriorAlgebra.map ((block j : W ≃ₗ[K] W) : W →ₗ[K] W)).toLinearMap := by
    intro j
    by_cases hji : j = i
    · subst hji
      ext x
      simp [xj, block, ExteriorAlgebra.map_id]
    · simpa [xj, block, hji] using
        (Classical.choose_spec
          (exists_basisScalingLinearEquiv_two_updateCliffordUnit_eq_exteriorMap
            (K := K) (V := V) (W := W) b (i := j) (j := i) hji (a := t j))).2.2
  have hunitaryj :
      ∀ j,
        (((xj j : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [xj]
    · simpa [xj, hji] using
        (Classical.choose_spec
          (exists_basisScalingLinearEquiv_two_updateCliffordUnit_eq_exteriorMap
            (K := K) (V := V) (W := W) b (i := j) (j := i) hji (a := t j))).1
  have hevenj :
      ∀ j,
        (((xj j : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [xj]
    · simpa [xj, hji] using
        (Classical.choose_spec
          (exists_basisScalingLinearEquiv_two_updateCliffordUnit_eq_exteriorMap
            (K := K) (V := V) (W := W) b (i := j) (j := i) hji (a := t j))).2.1
  have hunitary :
      (((L.map xj).prod : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) := by
    induction L with
    | nil =>
        simp
    | cons j L ih =>
        simp only [List.map_cons, List.prod_cons, Units.val_mul]
        exact Submonoid.mul_mem _ (hunitaryj j) ih
  have heven :
      (((L.map xj).prod : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
        CliffordAlgebra (QuadraticForm.dualProd K W)) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) := by
    induction L with
    | nil =>
        simp
    | cons j L ih =>
        simp only [List.map_cons, List.prod_cons, Units.val_mul]
        exact (CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem (hevenj j) ih
  have haction :
      splitCliffordAction (K := K) W
          ((((L.map xj).prod : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W))) =
        (ExteriorAlgebra.map
          ((((L.map block).prod : W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
    simpa using
      (splitCliffordAction_list_prod_unit_eq_exteriorMap_prod_of_forall
        (K := K) (V := V) (W := W) L xj block hxj)
  let ublock : ι → W ≃ₗ[K] W := fun j =>
    basisScalingLinearEquiv (K := K) (W := W) b
      (Function.update (Function.update (fun _ => (1 : Kˣ)) j (t j)) i (t j)⁻¹)
  have hpair :
      (s : Set ι).Pairwise fun j k => Commute (ublock j) (ublock k) := by
    simpa [s, ublock] using
      (basisScalingLinearEquiv_two_update_pairwise
        (K := K) (W := W) (b := b) (i := i) (t := t))
  have hpairBlock :
      (s : Set ι).Pairwise fun j k => Commute (block j) (block k) := by
    intro j hj k hk hjk
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simpa [block, ublock, hji, hki] using hpair hj hk hjk
  have hpairBlock_toFinset :
      (s.toList.toFinset : Set ι).Pairwise fun j k => Commute (block j) (block k) := by
    simpa [L] using hpairBlock
  have hLprod :
      (L.map block).prod = s.noncommProd block hpairBlock := by
    simpa [L, s, ublock] using
      (Finset.noncommProd_toFinset (l := s.toList) (f := block) hpairBlock_toFinset
        s.nodup_toList).symm
  have hsame :
      s.noncommProd block hpairBlock = s.noncommProd ublock hpair := by
    refine Finset.noncommProd_congr rfl ?_ hpairBlock
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [block, ublock, hji]
  have hscale :
      (L.map block).prod = basisScalingLinearEquiv (K := K) (W := W) b t := by
    rw [hLprod, hsame]
    simpa [s, ublock] using
      (basisScalingLinearEquiv_eq_noncommProd_two_update_of_prod_eq_one
        (K := K) (W := W) (b := b) (i := i) (t := t) hprod).symm
  refine ⟨(L.map xj).prod, hunitary, heven, ?_⟩
  simpa [hscale] using haction

omit [FiniteDimensional K V] in
/-- On the split exterior model, the explicit two-reflection lift of a chosen-line square scaling
acts on the vacuum vector by the normalized scalar `-(b / a)`. -/
theorem splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_apply_one_lineScaling
    {W : Submodule K V} [FiniteDimensional K W]
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (a b : Kˣ) :
    splitCliffordAction (K := K) W
        (((spinIotaPairOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
            (-(((a : K)⁻¹) • f), (a : K) • w)
            (-(((b : K)⁻¹) • f), (b : K) • w)
            (by simp [QuadraticForm.dualProd, hf])
            (by simp [QuadraticForm.dualProd, hf]) : spinGroup (QuadraticForm.dualProd K W)) :
          CliffordAlgebra (QuadraticForm.dualProd K W))) 1 =
      (-(b / a : K)) • (1 : IsotropicExteriorModel (K := K) W) := by
  let x :
      Module.Dual K W × W := (-(((a : K)⁻¹) • f), (a : K) • w)
  let y :
      Module.Dual K W × W := (-(((b : K)⁻¹) • f), (b : K) • w)
  have hy1 : splitGeneratorAction (K := K) W y 1 = (b : K) • ExteriorAlgebra.ι K w := by
    have hcontr :
        contractionAction (K := K) W (-(((b : K)⁻¹) • f)) (1 : IsotropicExteriorModel (K := K) W) =
          0 := by
      simpa using
        contractionAction_algebraMap (K := K) (W := W) (d := -(((b : K)⁻¹) • f)) (r := (1 : K))
    rw [show splitGeneratorAction (K := K) W y 1 =
        contractionAction (K := K) W (-(((b : K)⁻¹) • f)) 1 +
          wedgeAction (K := K) W ((b : K) • w) 1 by
          rfl]
    rw [hcontr, zero_add, wedgeAction_apply]
    simp [Algebra.smul_def]
  calc
    splitCliffordAction (K := K) W
        (((spinIotaPairOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
            (-(((a : K)⁻¹) • f), (a : K) • w)
            (-(((b : K)⁻¹) • f), (b : K) • w)
            (by simp [QuadraticForm.dualProd, hf])
            (by simp [QuadraticForm.dualProd, hf]) : spinGroup (QuadraticForm.dualProd K W)) :
          CliffordAlgebra (QuadraticForm.dualProd K W))) 1
      = splitGeneratorAction (K := K) W x
          (splitGeneratorAction (K := K) W y 1) := by
            simp [x, y, coe_spinIotaPairOfQuadraticEqNegOne, splitCliffordAction_apply_ι, map_mul]
  _ = splitGeneratorAction (K := K) W x ((b : K) • ExteriorAlgebra.ι K w) := by
        rw [hy1]
  _ = (-(b / a : K)) • (1 : IsotropicExteriorModel (K := K) W) := by
        have hsingle_zero :
            wedgeAction (K := K) W ((a : K) • w) (ExteriorAlgebra.ι K w) = 0 := by
          rw [wedgeAction_apply]
          simp [Algebra.smul_def, mul_assoc]
        have hwedge_zero :
            wedgeAction (K := K) W ((a : K) • w) ((b : K) • ExteriorAlgebra.ι K w) = 0 := by
          rw [map_smul, hsingle_zero, smul_zero]
        rw [show splitGeneratorAction (K := K) W x ((b : K) • ExteriorAlgebra.ι K w) =
            contractionAction (K := K) W (-(((a : K)⁻¹) • f))
                ((b : K) • ExteriorAlgebra.ι K w) +
              wedgeAction (K := K) W ((a : K) • w) ((b : K) • ExteriorAlgebra.ι K w) by
              rfl]
        rw [map_smul, contractionAction_ι, hwedge_zero, add_zero]
        simp [hf, Algebra.smul_def, div_eq_mul_inv]

/-- The explicit two-reflection lift of a chosen-line square scaling acts exactly as the natural
exterior action, normalized by the scalar `-(b / a)`. -/
theorem splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_eq_smul_exteriorMap_lineScaling
    {W : Submodule K V} [FiniteDimensional K W]
    (f : Module.Dual K W) (w : W) (hf : f w = 1) (a b : Kˣ) :
    splitCliffordAction (K := K) W
        (((spinIotaPairOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
            (-(((a : K)⁻¹) • f), (a : K) • w)
            (-(((b : K)⁻¹) • f), (b : K) • w)
            (by simp [QuadraticForm.dualProd, hf])
            (by simp [QuadraticForm.dualProd, hf]) : spinGroup (QuadraticForm.dualProd K W)) :
          CliffordAlgebra (QuadraticForm.dualProd K W))) =
      (-(b / a : K)) •
        (ExteriorAlgebra.map
          ((lineScalingLinearEquiv (f := f) (w := w) hf ((a / b) ^ 2)) : W →ₗ[K] W)).toLinearMap := by
  let s : spinGroup (QuadraticForm.dualProd K W) :=
    spinIotaPairOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
      (-(((a : K)⁻¹) • f), (a : K) • w)
      (-(((b : K)⁻¹) • f), (b : K) • w)
      (by simp [QuadraticForm.dualProd, hf])
      (by simp [QuadraticForm.dualProd, hf])
  let g : W ≃ₗ[K] W := lineScalingLinearEquiv (f := f) (w := w) hf ((a / b) ^ 2)
  have hs :
      spinSpecialOrthogonalRepresentationFiniteDimensional (Q := QuadraticForm.dualProd K W) s =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g := by
    change
      spinSpecialOrthogonalPairGenerator (Q := QuadraticForm.dualProd K W)
          (-(((a : K)⁻¹) • f), (a : K) • w)
          (-(((b : K)⁻¹) • f), (b : K) • w)
          (by simp [QuadraticForm.dualProd, hf])
          (by simp [QuadraticForm.dualProd, hf]) =
        dualProdSpecialOrthogonalOfLinearEquiv (K := K) g
    simpa [g] using
      spinSpecialOrthogonalPairGenerator_eq_lineScalingLinearEquiv
        (K := K) (W := W) (f := f) (w := w) hf (a := a) (b := b)
  obtain ⟨c, hc⟩ :=
    splitCliffordAction_eq_smul_exteriorMap_of_spinSpecialOrthogonalRepresentation_eq
      (K := K) (V := V) s g hs
  have hpair :
      splitCliffordAction (K := K) W
          ((s : spinGroup (QuadraticForm.dualProd K W)) :
            CliffordAlgebra (QuadraticForm.dualProd K W)) 1 =
        (-(b / a : K)) • (1 : IsotropicExteriorModel (K := K) W) := by
    simpa [s] using
      splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_apply_one_lineScaling
        (K := K) (V := V) (f := f) (w := w) hf (a := a) (b := b)
  have hc1 :
      algebraMap K (IsotropicExteriorModel (K := K) W) c =
        algebraMap K (IsotropicExteriorModel (K := K) W) (-(b / a : K)) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (congrArg
        (fun A : Module.End K (IsotropicExteriorModel (K := K) W) =>
          A (1 : IsotropicExteriorModel (K := K) W))
        hc).symm.trans hpair
  have hcoeff : c = -(b / a : K) :=
    (algebraMap K (IsotropicExteriorModel (K := K) W)).injective hc1
  simpa [s, g, hcoeff] using hc

/-- A square-determinant basis scaling admits an explicit even unitary Clifford lift whose split
action is the normalized exterior action, with scalar `-(1 / u)` for the chosen square root
`u` of the determinant. -/
theorem exists_basisScalingLinearEquivCliffordUnit_eq_smul_exteriorMap_of_prod_eq_sq
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (t : ι → Kˣ) (u : Kˣ)
    (hprod : (∏ j, t j) = u ^ 2) :
    ∃ x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ,
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (-(1 / (u : K) : K)) •
          (ExteriorAlgebra.map
            (((basisScalingLinearEquiv (K := K) (W := W) b t : W ≃ₗ[K] W) :
                W →ₗ[K] W))).toLinearMap := by
  classical
  let s : ι → Kˣ := Function.update t i (t i / u ^ 2)
  have hsprod : (∏ j, s j) = 1 := by
    have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have hsupdate :
        (∏ j, s j) = (t i / u ^ 2) * (Finset.univ.erase i).prod fun j => t j := by
      simpa only [s, Finset.erase_eq] using
        (Finset.prod_update_of_mem (s := Finset.univ) (i := i) hi t (t i / u ^ 2))
    calc
      (∏ j, s j) = (t i / u ^ 2) * (Finset.univ.erase i).prod fun j => t j := hsupdate
      _ = (t i / u ^ 2) * ((∏ j, t j) / t i) := by
        rw [Finset.prod_erase_eq_div (s := Finset.univ) (f := t) hi]
      _ = 1 := by
        rw [hprod]
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hsplit : t = (Function.update (1 : ι → Kˣ) i (u ^ 2)) * s := by
    funext k
    apply Units.ext
    by_cases hki : k = i
    · subst hki
      simp [s, Function.update, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    · simp [s, Function.update, hki]
  have hscale :
      basisScalingLinearEquiv (K := K) (W := W) b t =
        lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2) *
          basisScalingLinearEquiv (K := K) (W := W) b s := by
    calc
      basisScalingLinearEquiv (K := K) (W := W) b t =
          basisScalingLinearEquiv (K := K) (W := W) b
            ((Function.update (1 : ι → Kˣ) i (u ^ 2)) * s) := by
              rw [hsplit]
      _ = basisScalingLinearEquiv (K := K) (W := W) b (Function.update (1 : ι → Kˣ) i (u ^ 2)) *
            basisScalingLinearEquiv (K := K) (W := W) b s := by
              rw [basisScalingLinearEquiv_mul]
      _ = lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2) *
            basisScalingLinearEquiv (K := K) (W := W) b s := by
              rw [basisScalingLinearEquiv_update_eq_lineScalingLinearEquiv]
  let gline : spinGroup (QuadraticForm.dualProd K W) :=
    spinIotaPairOfQuadraticEqNegOne (Q := QuadraticForm.dualProd K W)
      (-(((u : K)⁻¹) • b.coord i), (u : K) • b i)
      (-((((1 : Kˣ) : K)⁻¹) • b.coord i), (((1 : Kˣ) : K)) • b i)
      (by simp [QuadraticForm.dualProd, Module.Basis.coord_apply])
      (by simp [QuadraticForm.dualProd, Module.Basis.coord_apply])
  let xline : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ := spinGroup.toUnits gline
  have hline_unitary :
      ((xline : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) := by
    have hxline : IsUnit (xline : CliffordAlgebra (QuadraticForm.dualProd K W)) := xline.isUnit
    rw [hxline.mem_unitary_iff_star_mul_self]
    simpa [xline, gline] using (spinGroup.coe_star_mul_self gline)
  have hline_even :
      ((xline : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
        CliffordAlgebra.even (QuadraticForm.dualProd K W) := by
    simpa [xline, gline] using spinGroup.mem_even gline.property
  have hline_action :
      splitCliffordAction (K := K) W
          (xline : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (-(1 / (u : K) : K)) •
          (ExteriorAlgebra.map
            ((lineScalingLinearEquiv (f := b.coord i) (w := b i)
                (by simp [Module.Basis.coord_apply]) (u ^ 2)) : W →ₗ[K] W)).toLinearMap := by
    simpa [xline, gline] using
      (splitCliffordAction_spinIotaPairOfQuadraticEqNegOne_eq_smul_exteriorMap_lineScaling
        (K := K) (W := W) (f := b.coord i) (w := b i)
        (by simp [Module.Basis.coord_apply]) (a := u) (b := (1 : Kˣ)))
  rcases
      exists_basisScalingLinearEquivCliffordUnit_eq_exteriorMap_of_prod_eq_one
        (K := K) (W := W) (b := b) (i := i) (t := s) hsprod with
    ⟨y, hy_unitary, hy_even, hy_action⟩
  refine ⟨xline * y, ?_, ?_, ?_⟩
  · exact Submonoid.mul_mem _ hline_unitary hy_unitary
  · exact (CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem hline_even hy_even
  · have hxy :
        splitCliffordAction (K := K) W
            (((xline * y : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
              CliffordAlgebra (QuadraticForm.dualProd K W))) =
          ((-(1 / (u : K) : K)) * 1) •
            (ExteriorAlgebra.map
              (((lineScalingLinearEquiv (f := b.coord i) (w := b i)
                    (by simp [Module.Basis.coord_apply]) (u ^ 2) *
                  basisScalingLinearEquiv (K := K) (W := W) b s : W ≃ₗ[K] W) :
                  W →ₗ[K] W))).toLinearMap := by
      simpa using
        (splitCliffordAction_mul_eq_smul_exteriorMap_mul_of_eq_smul_exteriorMap
          (K := K) (V := V) (W := W)
          (x := (xline : CliffordAlgebra (QuadraticForm.dualProd K W)))
          (y := (y : CliffordAlgebra (QuadraticForm.dualProd K W)))
          (c := -(1 / (u : K) : K)) (d := 1)
          (e := lineScalingLinearEquiv (f := b.coord i) (w := b i)
            (by simp [Module.Basis.coord_apply]) (u ^ 2))
          (f := basisScalingLinearEquiv (K := K) (W := W) b s)
          hline_action (by simpa using hy_action))
    simpa [hscale] using hxy

/-- Any linear equivalence with square determinant admits an explicit even unitary Clifford lift
whose split action is the normalized exterior action, with scalar `-(1 / u)` for a chosen square
root `u` of the determinant. -/
theorem exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_det_eq_sq
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (i : ι) (e : W ≃ₗ[K] W) (u : Kˣ)
    (hdet : LinearEquiv.det e = u ^ 2) :
    ∃ x : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ,
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          unitary (CliffordAlgebra (QuadraticForm.dualProd K W)) ∧
      ((x : CliffordAlgebra (QuadraticForm.dualProd K W))) ∈
          CliffordAlgebra.even (QuadraticForm.dualProd K W) ∧
      splitCliffordAction (K := K) W
          (x : CliffordAlgebra (QuadraticForm.dualProd K W)) =
        (-(1 / (u : K) : K)) •
          (ExteriorAlgebra.map ((e : W →ₗ[K] W))).toLinearMap := by
  classical
  rcases
      linearEquiv_eq_list_basisTransvection_mul_basisScalingLinearEquiv_mul_list_basisTransvection_of_det_eq_sq
        (K := K) (W := W) (b := b) (e := e) (u := u) hdet with
    ⟨L, L', t, htprod, he⟩
  rcases
      exists_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
        (K := K) (V := V) (W := W) (b := b) L with
    ⟨xL, hxL_unitary, hxL_even, hxL_action⟩
  rcases
      exists_basisScalingLinearEquivCliffordUnit_eq_smul_exteriorMap_of_prod_eq_sq
        (K := K) (V := V) (W := W) (b := b) (i := i) (t := t) (u := u) htprod with
    ⟨xM, hxM_unitary, hxM_even, hxM_action⟩
  rcases
      exists_list_prod_basisTransvectionCliffordUnit_eq_exteriorMap_prod
        (K := K) (V := V) (W := W) (b := b) L' with
    ⟨xR, hxR_unitary, hxR_even, hxR_action⟩
  refine ⟨xL * xM * xR, ?_, ?_, ?_⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hxL_unitary hxM_unitary) hxR_unitary
  · exact (CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem
      ((CliffordAlgebra.even (QuadraticForm.dualProd K W)).mul_mem hxL_even hxM_even) hxR_even
  · let eL : W ≃ₗ[K] W := (L.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod
    let eM : W ≃ₗ[K] W := basisScalingLinearEquiv (K := K) (W := W) b t
    let eR : W ≃ₗ[K] W := (L'.map (basisTransvectionLinearEquiv (K := K) (W := W) b)).prod
    have hxLM :
        splitCliffordAction (K := K) W
            (((xL * xM : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
              CliffordAlgebra (QuadraticForm.dualProd K W))) =
          (1 * (-(1 / (u : K) : K))) •
            (ExteriorAlgebra.map (((eL * eM : W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
      simpa [eL, eM] using
        (splitCliffordAction_mul_eq_smul_exteriorMap_mul_of_eq_smul_exteriorMap
          (K := K) (V := V) (W := W)
          (x := (xL : CliffordAlgebra (QuadraticForm.dualProd K W)))
          (y := (xM : CliffordAlgebra (QuadraticForm.dualProd K W)))
          (c := (1 : K)) (d := -(1 / (u : K) : K))
          (e := eL) (f := eM)
          (by simpa [eL] using hxL_action) hxM_action)
    have hxLMR :
        splitCliffordAction (K := K) W
            ((((xL * xM) * xR : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
              CliffordAlgebra (QuadraticForm.dualProd K W))) =
          ((1 * (-(1 / (u : K) : K))) * 1) •
            (ExteriorAlgebra.map ((((eL * eM) * eR : W ≃ₗ[K] W) : W →ₗ[K] W))).toLinearMap := by
      simpa [eL, eM, eR, mul_assoc] using
        (splitCliffordAction_mul_eq_smul_exteriorMap_mul_of_eq_smul_exteriorMap
          (K := K) (V := V) (W := W)
          (x := (((xL * xM : (CliffordAlgebra (QuadraticForm.dualProd K W))ˣ) :
            CliffordAlgebra (QuadraticForm.dualProd K W))))
          (y := (xR : CliffordAlgebra (QuadraticForm.dualProd K W)))
          (c := 1 * (-(1 / (u : K) : K))) (d := (1 : K))
          (e := eL * eM) (f := eR)
          hxLM (by simpa [eR] using hxR_action))
    have he' : ((eL * eM) * eR : W ≃ₗ[K] W) = e := by
      simpa [eL, eM, eR, mul_assoc] using he.symm
    simpa [he', mul_assoc] using hxLMR

/-- If every unit of the base field is a square, then every higher-rank Levi automorphism admits
an explicit even unitary Clifford lift whose split action is a normalized exterior action. This
removes the square-determinant hypothesis from
`exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_det_eq_sq`, while still staying at the
chosen Clifford-unit level rather than asserting membership in the ambient spin image. -/
theorem exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_square_surjective
    {ι : Type*} {W : Submodule K V} [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (hsq : Function.Surjective (powMonoidHom (α := Kˣ) 2))
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
          (ExteriorAlgebra.map ((e : W →ₗ[K] W))).toLinearMap := by
  rcases hsq (LinearEquiv.det e) with ⟨u, hu⟩
  rcases
      exists_linearEquivCliffordUnit_eq_smul_exteriorMap_of_det_eq_sq
        (K := K) (V := V) (W := W) (b := b) (i := i) (e := e) (u := u) hu.symm with
    ⟨x, hx_unitary, hx_even, hx_action⟩
  exact ⟨u, x, hu.symm, hx_unitary, hx_even, hx_action⟩

end SplitTransport

section WittModel

variable [FiniteDimensional K V]

/-- The transported hyperbolic Clifford action on the canonical Witt model. -/
noncomputable def wittHyperbolicCliffordAction (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  hyperbolicCliffordAction (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic Clifford action on the canonical Witt model is faithful. -/
theorem wittHyperbolicCliffordAction_injective (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Function.Injective (wittHyperbolicCliffordAction (K := K) Q e) := by
  exact hyperbolicCliffordAction_injective
    (K := K) (Q := Q) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation on the canonical Witt model. -/
noncomputable def wittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  hyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation restricted to the even Witt summand. -/
noncomputable abbrev evenWittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  evenHyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin representation restricted to the odd Witt summand. -/
noncomputable abbrev oddWittHyperbolicSpinRepresentation (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :=
  oddHyperbolicSpinRepresentation (K := K) (W := Q.wittSubspace) e

/-- The transported hyperbolic spin action preserves the even half of the canonical Witt model. -/
theorem wittHyperbolicSpinRepresentation_mem_evenWittExterior (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ evenWittExterior (K := K) Q) :
    wittHyperbolicSpinRepresentation (K := K) Q e g x ∈ evenWittExterior (K := K) Q := by
  exact hyperbolicSpinRepresentation_mem_evenExteriorSubmodule (K := K) (W := Q.wittSubspace) e hx

/-- The transported hyperbolic spin action preserves the odd half of the canonical Witt model. -/
theorem wittHyperbolicSpinRepresentation_mem_oddWittExterior (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace))
    {g : spinGroup Q}
    {x : WittExteriorModel (K := K) Q} (hx : x ∈ oddWittExterior (K := K) Q) :
    wittHyperbolicSpinRepresentation (K := K) Q e g x ∈ oddWittExterior (K := K) Q := by
  exact hyperbolicSpinRepresentation_mem_oddExteriorSubmodule (K := K) (W := Q.wittSubspace) e hx

end WittModel

end HyperbolicTransport

section SplitUnitGenerator

variable [FiniteDimensional K V]
variable {W : Submodule K V}

/-- If `W` is nonzero, one can choose a split generator with square equal to the identity. -/
lemma exists_splitUnitGenerator (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    ∃ d : Module.Dual K W, ∃ w : W, d w = 1 := by
  let b := Module.finBasis K W
  let i : Fin (Module.finrank K W) := ⟨0, hW⟩
  refine ⟨b.coord i, b i, ?_⟩
  simp [b, i]
end SplitUnitGenerator

section SplitGeneratorInvolution

variable [Invertible (2 : K)]
variable {W : Submodule K V}

/-- A split generator with `d(w) = 1` acts as an involution on `⋀W`. -/
lemma splitGeneratorAction_sq_apply_of_dual_one (W : Submodule K V)
    (d : Module.Dual K W) (w : W)
    (h : d w = 1) (x : IsotropicExteriorModel (K := K) W) :
    splitGeneratorAction (K := K) W (d, w)
        (splitGeneratorAction (K := K) W (d, w) x) = x := by
  simpa [QuadraticForm.dualProd, h] using
    splitGeneratorAction_sq_apply (K := K) (W := W) (d := d) (w := w) (x := x)

end SplitGeneratorInvolution

section EvenOddDimensions

variable [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {W : Submodule K V}

/-- For positive Witt index, a split unit generator swaps the chosen even and odd halves of `⋀W`. -/
noncomputable def evenOddSwapEquiv (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    evenExteriorSubmodule (K := K) W ≃ₗ[K] oddExteriorSubmodule (K := K) W := by
  classical
  let d : Module.Dual K W := Classical.choose (exists_splitUnitGenerator (K := K) W hW)
  let w : W := Classical.choose (Classical.choose_spec (exists_splitUnitGenerator (K := K) W hW))
  have hdw : d w = 1 :=
    Classical.choose_spec (Classical.choose_spec (exists_splitUnitGenerator (K := K) W hW))
  let toOdd : evenExteriorSubmodule (K := K) W →ₗ[K] oddExteriorSubmodule (K := K) W :=
    { toFun := fun x => ⟨splitGeneratorAction (K := K) W (d, w) x,
        splitGeneratorAction_mem_oddExteriorSubmodule (K := K) (W := W) (d, w) x.property⟩
      map_add' := by
        intro x y
        ext
        simp [map_add]
      map_smul' := by
        intro a x
        ext
        simp [map_smul] }
  let toEven : oddExteriorSubmodule (K := K) W →ₗ[K] evenExteriorSubmodule (K := K) W :=
    { toFun := fun x => ⟨splitGeneratorAction (K := K) W (d, w) x,
        splitGeneratorAction_mem_evenExteriorSubmodule (K := K) (W := W) (d, w) x.property⟩
      map_add' := by
        intro x y
        ext
        simp [map_add]
      map_smul' := by
        intro a x
        ext
        simp [map_smul] }
  refine
    { toLinearMap := toOdd
      invFun := toEven
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    ext
    exact splitGeneratorAction_sq_apply_of_dual_one (K := K) (W := W) d w hdw x
  · intro x
    ext
    exact splitGeneratorAction_sq_apply_of_dual_one (K := K) (W := W) d w hdw x

/-- For positive Witt index, the chosen even and odd halves of `⋀W` have the same dimension. -/
theorem finrank_evenExterior_eq_finrank_oddExterior (W : Submodule K V)
    (hW : 0 < Module.finrank K W) :
    Module.finrank K (evenExteriorSubmodule (K := K) W) =
      Module.finrank K (oddExteriorSubmodule (K := K) W) := by
  exact LinearEquiv.finrank_eq (evenOddSwapEquiv (K := K) W hW)

/-- For positive Witt index, the chosen even half of `⋀W` has dimension `2^(dim W - 1)`. -/
theorem finrank_evenExterior (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    Module.finrank K (evenExteriorSubmodule (K := K) W) = 2 ^ (Module.finrank K W - 1) := by
  let b := Module.finBasis K W
  letI : FiniteDimensional K (IsotropicExteriorModel (K := K) W) :=
    b.ExteriorAlgebra.finiteDimensional_of_finite
  letI : FiniteDimensional K (evenExteriorSubmodule (K := K) W) := by infer_instance
  letI : FiniteDimensional K (oddExteriorSubmodule (K := K) W) := by infer_instance
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (evenExteriorSubmodule (K := K) W) (oddExteriorSubmodule (K := K) W)
  rw [evenExteriorSubmodule_sup_oddExteriorSubmodule, evenExteriorSubmodule_inf_oddExteriorSubmodule,
    finrank_top, finrank_bot, add_zero, finrank_isotropicExteriorModel] at hsum
  have hEq := finrank_evenExterior_eq_finrank_oddExterior (K := K) W hW
  have hsum' : Module.finrank K (evenExteriorSubmodule (K := K) W) +
      Module.finrank K (evenExteriorSubmodule (K := K) W) = 2 ^ Module.finrank K W := by
    simpa [hEq] using hsum.symm
  have hpow : 2 ^ Module.finrank K W = 2 * 2 ^ (Module.finrank K W - 1) := by
    have hW0 : Module.finrank K W ≠ 0 := Nat.ne_of_gt hW
    rcases Nat.exists_eq_succ_of_ne_zero hW0 with ⟨n, hn⟩
    rw [hn]
    simp [pow_succ, mul_comm]
  have hsum'' : 2 * Module.finrank K (evenExteriorSubmodule (K := K) W) =
      2 ^ Module.finrank K W := by
    simpa [two_mul] using hsum'
  have htwice : 2 * Module.finrank K (evenExteriorSubmodule (K := K) W) =
      2 * 2 ^ (Module.finrank K W - 1) := hsum''.trans hpow
  have htwice' : Module.finrank K (evenExteriorSubmodule (K := K) W) * 2 =
      2 ^ (Module.finrank K W - 1) * 2 := by
    simpa [mul_comm] using htwice
  exact Nat.mul_right_cancel (by decide : 0 < 2) htwice'

/-- For positive Witt index, the chosen odd half of `⋀W` has dimension `2^(dim W - 1)`. -/
theorem finrank_oddExterior (W : Submodule K V) (hW : 0 < Module.finrank K W) :
    Module.finrank K (oddExteriorSubmodule (K := K) W) = 2 ^ (Module.finrank K W - 1) := by
  rw [← finrank_evenExterior_eq_finrank_oddExterior (K := K) W hW]
  exact finrank_evenExterior (K := K) W hW

end EvenOddDimensions

section HyperbolicDimensions

variable {Q : QuadraticForm K V} {W : Submodule K V}

section SplitIsotropicSubmodule

/-- The standard totally isotropic factor `0 × W` inside the split hyperbolic space `W* × W`. -/
def splitIsotropicSubmodule (W : Submodule K V) : Submodule K (Module.Dual K W × W) :=
  LinearMap.range (LinearMap.inr K (Module.Dual K W) W)

/-- The standard split factor `0 × W` is totally isotropic in `W* × W`. -/
theorem splitIsotropicSubmodule_isTotallyIsotropic (W : Submodule K V) :
    (QuadraticForm.dualProd K W).IsTotallyIsotropic (splitIsotropicSubmodule (K := K) (V := V) W) := by
  intro x
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨w, rfl⟩
  simp [QuadraticForm.dualProd]

/-- An explicit hyperbolic presentation carries the standard split factor to an ambient subspace. -/
def hyperbolicIsotropicSubmodule {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) : Submodule K V :=
  (splitIsotropicSubmodule (K := K) (V := V) W).map e.symm.toLinearMap

/-- The isotropic subspace carried by an explicit hyperbolic presentation is totally isotropic. -/
theorem hyperbolicIsotropicSubmodule_isTotallyIsotropic {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.IsTotallyIsotropic (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) := by
  dsimp [hyperbolicIsotropicSubmodule]
  exact (splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W).map e.symm

/-- The isotropic subspace carried by an explicit hyperbolic presentation has the expected rank. -/
theorem finrank_hyperbolicIsotropicSubmodule {Q : QuadraticForm K V} {W : Submodule K V}
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) =
      Module.finrank K W := by
  dsimp [hyperbolicIsotropicSubmodule]
  calc
    Module.finrank K ((splitIsotropicSubmodule (K := K) (V := V) W).map e.symm.toLinearMap) =
        Module.finrank K (splitIsotropicSubmodule (K := K) (V := V) W) := by
          exact LinearEquiv.finrank_map_eq e.symm.toLinearEquiv _
    _ = Module.finrank K W := by
      simpa [splitIsotropicSubmodule] using
        LinearMap.finrank_range_of_inj
          (f := LinearMap.inr K (Module.Dual K W) W)
          LinearMap.inr_injective

@[simp] theorem hyperbolicIsotropicSubmodule_splitIsometryEquivOfIsCompl
    [FiniteDimensional K V] [Invertible (2 : K)] {Q : QuadraticForm K V} {W U : Submodule K V}
    (hQ : Q.Nondegenerate) (hW : Q.IsTotallyIsotropic W)
    (hsplit : Module.finrank K V = 2 * Module.finrank K W) (hWU : IsCompl W U) :
    hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W)
      (QuadraticForm.splitIsometryEquivOfIsCompl (K := K) (Q := Q) (W := W) (U := U)
        hQ hW hsplit hWU) = W := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    rcases hx with ⟨w, rfl⟩
    simp [QuadraticForm.splitIsometryEquivOfIsCompl_symm_inr
      (K := K) (Q := Q) (W := W) (U := U) hQ hW hsplit hWU w]
  · intro hv
    refine ⟨(0, ⟨v, hv⟩), ?_, ?_⟩
    · exact ⟨⟨v, hv⟩, rfl⟩
    · exact
        (QuadraticForm.splitIsometryEquivOfIsCompl_symm_inr (K := K) (Q := Q) (W := W) (U := U)
          hQ hW hsplit hWU ⟨v, hv⟩)

end SplitIsotropicSubmodule

section HyperbolicWittIndex

variable [Invertible (2 : K)]

/-- The split hyperbolic form on `W* × W` is nondegenerate. -/
theorem dualProd_nondegenerate (W : Submodule K V) :
    (QuadraticForm.dualProd K W).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  ext x
  constructor
  · intro hx
    rcases (QuadraticMap.mem_radical_iff'.mp hx) with ⟨hxQ, hxrad⟩
    have hxQ' : x.1 x.2 = 0 := by
      simpa [QuadraticForm.dualProd] using hxQ
    have hx₁ : x.1 = 0 := by
      ext w
      have htest := hxrad (0, w)
      simpa [QuadraticForm.dualProd, hxQ'] using htest
    have hx₂eval : Module.Dual.eval K W x.2 = 0 := by
      ext d
      have htest := hxrad (d, 0)
      simpa [QuadraticForm.dualProd, hxQ'] using htest
    have hx₂ : x.2 = 0 := Module.eval_apply_injective K (V := W) (by
      simpa using hx₂eval)
    ext <;> simp [hx₁, hx₂]
  · intro hx
    subst x
    simp

variable [FiniteDimensional K V]

/-- Any totally isotropic subspace of `W* × W` has dimension at most `dim(W)`. -/
theorem finrank_le_of_isTotallyIsotropic_dualProd
    {U : Submodule K (Module.Dual K W × W)}
    (hU : (QuadraticForm.dualProd K W).IsTotallyIsotropic U) :
    Module.finrank K U ≤ Module.finrank K W := by
  have hle :
      U ≤ LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    exact (QuadraticMap.associated_isOrtho (Q := QuadraticForm.dualProd K W)).2
      (hU.isOrtho ⟨v, hv⟩ ⟨u, hu⟩)
  have hUorth :
      Module.finrank K U ≤
        Module.finrank K (LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U) :=
    Submodule.finrank_mono hle
  have horth :
      Module.finrank K (LinearMap.BilinForm.orthogonal (QuadraticForm.dualProd K W).associated U) =
        Module.finrank K (Module.Dual K W × W) - Module.finrank K U := by
    simpa using
      (LinearMap.BilinForm.finrank_orthogonal
        ((QuadraticMap.nondegenerate_associated_iff (Q := QuadraticForm.dualProd K W)).2
          (dualProd_nondegenerate (K := K) (V := V) W))
        U)
  have hambient : Module.finrank K (Module.Dual K W × W) = 2 * Module.finrank K W := by
    rw [Module.finrank_prod, Subspace.dual_finrank_eq]
    ring
  have hbound :
      Module.finrank K U ≤ Module.finrank K (Module.Dual K W × W) - Module.finrank K U := by
    rwa [horth] at hUorth
  omega

end HyperbolicWittIndex

variable [FiniteDimensional K V]

/-- An explicitly hyperbolic quadratic space has twice the dimension of the chosen isotropic model. -/
theorem finrank_eq_twice_finrank_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K V = 2 * Module.finrank K W := by
  calc
    Module.finrank K V = Module.finrank K (Module.Dual K W × W) :=
      LinearEquiv.finrank_eq e.toLinearEquiv
    _ = Module.finrank K (Module.Dual K W) + Module.finrank K W := Module.finrank_prod
    _ = 2 * Module.finrank K W := by rw [Subspace.dual_finrank_eq]; ring

/-- In the explicit hyperbolic case, the chosen `⋀W` model has the expected spinor dimension. -/
theorem finrank_isotropicExteriorModel_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Module.finrank K (IsotropicExteriorModel (K := K) W) = 2 ^ (Module.finrank K V / 2) := by
  rw [finrank_isotropicExteriorModel,
    finrank_eq_twice_finrank_of_hyperbolic (K := K) (Q := Q) (W := W) e]
  simp

section HyperbolicWittIndex

variable [Invertible (2 : K)]

/-- Any explicit hyperbolic presentation `Q ≃ dualProd K W` realizes the full Witt index. -/
theorem wittIndex_eq_finrank_of_hyperbolic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.wittIndex = Module.finrank K W := by
  let splitIsotropic := splitIsotropicSubmodule (K := K) (V := V) W
  have hsplit : (QuadraticForm.dualProd K W).IsTotallyIsotropic splitIsotropic := by
    simpa [splitIsotropic] using splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W
  have hpre :
      Q.IsTotallyIsotropic (splitIsotropic.map e.symm.toLinearMap) := by
    exact hsplit.map e.symm
  have hlower : Module.finrank K W ≤ Q.wittIndex := by
    calc
      Module.finrank K W = Module.finrank K splitIsotropic := by
        simpa [splitIsotropic] using
          (LinearMap.finrank_range_of_inj
            (f := LinearMap.inr K (Module.Dual K W) W)
            LinearMap.inr_injective).symm
      _ = Module.finrank K (splitIsotropic.map e.symm.toLinearMap) := by
        symm
        exact LinearEquiv.finrank_map_eq e.symm.toLinearEquiv splitIsotropic
      _ ≤ Q.wittIndex := Q.finrank_le_wittIndex hpre
  have hmap :
      (QuadraticForm.dualProd K W).IsTotallyIsotropic (Q.wittSubspace.map e.toLinearMap) := by
    intro x
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact (e.map_app y).trans (Q.wittSubspace_isTotallyIsotropic ⟨y, hy⟩)
  have hupper : Q.wittIndex ≤ Module.finrank K W := by
    calc
      Q.wittIndex = Module.finrank K Q.wittSubspace := by rw [Q.finrank_wittSubspace]
      _ = Module.finrank K (Q.wittSubspace.map e.toLinearMap) := by
        symm
        exact LinearEquiv.finrank_map_eq e.toLinearEquiv Q.wittSubspace
      _ ≤ Module.finrank K W :=
        finrank_le_of_isTotallyIsotropic_dualProd (K := K) (V := V) (W := W) hmap
  exact Nat.le_antisymm hupper hlower

/-- The standard split factor `0 × W` realizes the full Witt index of `dualProd K W`. -/
theorem splitIsotropicSubmodule_isMaximalTotallyIsotropic (W : Submodule K V) :
    (QuadraticForm.dualProd K W).IsMaximalTotallyIsotropic
      (splitIsotropicSubmodule (K := K) (V := V) W) := by
  apply QuadraticForm.isMaximalTotallyIsotropic_of_finrank_eq_wittIndex
    (Q := QuadraticForm.dualProd K W)
  · exact splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W
  · apply Nat.le_antisymm
    · exact (QuadraticForm.dualProd K W).finrank_le_wittIndex
        (splitIsotropicSubmodule_isTotallyIsotropic (K := K) (V := V) W)
    · calc
        (QuadraticForm.dualProd K W).wittIndex ≤ Module.finrank K W := by
          simpa [QuadraticForm.finrank_wittSubspace] using
            finrank_le_of_isTotallyIsotropic_dualProd
              (K := K) (V := V) (W := W)
              ((QuadraticForm.dualProd K W).wittSubspace_isTotallyIsotropic)
        _ = Module.finrank K (splitIsotropicSubmodule (K := K) (V := V) W) := by
          simpa [splitIsotropicSubmodule] using
            (LinearMap.finrank_range_of_inj
              (f := LinearMap.inr K (Module.Dual K W) W)
              LinearMap.inr_injective).symm

/-- An explicit hyperbolic presentation carries the standard split factor to a maximal isotropic
subspace of the ambient quadratic space. -/
theorem hyperbolicIsotropicSubmodule_isMaximalTotallyIsotropic
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K W)) :
    Q.IsMaximalTotallyIsotropic (hyperbolicIsotropicSubmodule (K := K) (Q := Q) (W := W) e) := by
  dsimp [hyperbolicIsotropicSubmodule]
  exact (splitIsotropicSubmodule_isMaximalTotallyIsotropic (K := K) (V := V) W).map e.symm

end HyperbolicWittIndex

/-- An explicitly hyperbolic quadratic space has Witt index `dim(V) / 2`. -/
theorem wittIndex_eq_half_finrank_of_hyperbolic (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Q.wittIndex = Module.finrank K V / 2 := by
  rw [← Q.finrank_wittSubspace,
    finrank_eq_twice_finrank_of_hyperbolic (K := K) (Q := Q) (W := Q.wittSubspace) e]
  omega

/-- In the explicit hyperbolic case, the canonical Witt model has dimension `2 ^ (dim V / 2)`. -/
theorem finrank_wittExteriorModel_of_hyperbolic (Q : QuadraticForm K V)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (WittExteriorModel (K := K) Q) = 2 ^ (Module.finrank K V / 2) := by
  rw [finrank_wittExteriorModel, wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e]

section HalfSpinDimensions

variable [Invertible (2 : K)]

/-- In the split hyperbolic case, the even half-spin space has dimension `2^(dim(V)/2 - 1)`. -/
theorem finrank_evenWittExterior_of_hyperbolic (Q : QuadraticForm K V)
    (hQ : 0 < Q.wittIndex)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (evenWittExterior (K := K) Q) = 2 ^ (Module.finrank K V / 2 - 1) := by
  have hW : 0 < Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hQ
  simpa [evenWittExterior, Q.finrank_wittSubspace,
    wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e] using
    finrank_evenExterior (K := K) Q.wittSubspace hW

/-- In the split hyperbolic case, the odd half-spin space has dimension `2^(dim(V)/2 - 1)`. -/
theorem finrank_oddWittExterior_of_hyperbolic (Q : QuadraticForm K V)
    (hQ : 0 < Q.wittIndex)
    (e : Q.IsometryEquiv (QuadraticForm.dualProd K Q.wittSubspace)) :
    Module.finrank K (oddWittExterior (K := K) Q) = 2 ^ (Module.finrank K V / 2 - 1) := by
  have hW : 0 < Module.finrank K Q.wittSubspace := by
    simpa [Q.finrank_wittSubspace] using hQ
  simpa [oddWittExterior, Q.finrank_wittSubspace,
    wittIndex_eq_half_finrank_of_hyperbolic (K := K) Q e] using
    finrank_oddExterior (K := K) Q.wittSubspace hW

end HalfSpinDimensions

end HyperbolicDimensions

end Spinor
