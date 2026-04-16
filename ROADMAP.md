# SpinorLean — Roadmap

## Goal
First-ever formalization of spinor representations from Clifford algebras in a proof assistant.
Target venues: CPP 2027, ITP 2027, or *Advances in Applied Clifford Algebras*.

---

## Phase 1: Foundations (Week 1-2)

### 1.1 Project Setup
- [x] Lean 4 + Mathlib project via `lake init`
- [x] Verify Mathlib's `CliffordAlgebra`, `ExteriorAlgebra`, `SpinGroup` imports compile
- [x] Establish notation and convention file

### 1.2 Quadratic Spaces & Isotropic Subspaces
- [x] Define totally isotropic subspaces of a quadratic module (V, Q)
- [x] Prove existence of maximal isotropic subspaces for finite-dimensional spaces over fields
- [x] Witt decomposition: V ≅ W ⊕ W* ⊕ V₀ (hyperbolic splitting)
  - [x] Package the underlying linear decomposition `V ≃ W ⊕ W* ⊕ V₀` from a chosen
    complement, with canonical `wittSubspace` specializations and residual-dimension formulas
  - [x] Upgrade that linear decomposition to the orthogonal / hyperbolic quadratic-form splitting
  - [x] Package the resulting general quadratic Witt splitting as first-class presentation data and
    expose its orthogonal hyperbolic factor through the existing chosen-model APIs
- [x] Package the chosen-model transport once an explicit hyperbolic isometry `Q ≃ dualProd K W` is given
- [x] Prove any explicit hyperbolic presentation `Q ≃ dualProd K W` satisfies `wittIndex Q = dim W`
- [x] Package the maximal totally isotropic subspace determined by an explicit hyperbolic
  presentation `Q ≃ dualProd K W`
- [x] From a half-dimensional totally isotropic subspace `W` plus a chosen complement `U`,
  construct an explicit split isometry `Q ≃ dualProd K W`
- [x] In the nondegenerate doubled case, package the canonical split presentation
  `(Q.prod (-Q)) ≃ dualProd K Δ` using the diagonal isotropic subspace `Δ ≤ V × V`
- [x] In the doubled canonical split case, prove the diagonal subspace `Δ` realizes the Witt index
  and is maximal totally isotropic
- [x] Witt index and its basic properties

### 1.3 Mathlib Inventory
- [x] Audit `Mathlib.LinearAlgebra.CliffordAlgebra.*` — catalog what's available
- [x] Audit `Mathlib.LinearAlgebra.ExteriorAlgebra.*` — same
- [x] Audit `Mathlib.LinearAlgebra.QuadraticForm.*` — isotropic subspace API
- [x] Document gaps that need filling

---

## Phase 2: The Spinor Module (Week 2-4)

### 2.1 Exterior Algebra of Maximal Isotropic Subspace
- [x] Given W ≤ V maximal isotropic, construct ⋀W (exterior algebra on W)
- [x] Show dim(⋀W) = 2^n where n = dim(W) = Witt index

### 2.2 Clifford Action on ⋀W
- [x] Define the split hyperbolic action of `Cl(W* × W, dualProd)` on `⋀W`
- [x] Restrict that split hyperbolic action to `spinGroup (dualProd)`
- [ ] Define the left action of Cl(V, Q) on ⋀W
  - [x] Transport the split action along an explicit hyperbolic isometry `Q ≃ dualProd K W`
  - [x] Package explicit hyperbolic presentations `Q ≃ dualProd K W` as first-class chosen-model
    spinor data
  - [x] Expose those presented chosen models as actual `Module (CliffordAlgebra Q)` and
    `MulAction (spinGroup Q)` structures, including the canonical doubled case
  - [x] Package the chosen Witt-subspace case `Q ≃ dualProd K Q.wittSubspace` through the same
    presentation API
  - [x] Package the split-data case `(W,U)` through the same transport/presentation API
  - [x] In split rank, let the canonical Witt-subspace model choose a complement internally and
    build the transported action without an explicit isometry argument
  - [x] Specialize that transport canonically to the doubled form `Q ⊕ (-Q)` in the nondegenerate case
  - [x] Derive that isometry canonically from a full Witt decomposition `V ≃ W ⊕ W* ⊕ V₀`
  - For w ∈ W: action is exterior multiplication (w ∧ −)
  - For f ∈ W*: action is interior multiplication / contraction (ι_f)
  - Extend to all of Cl(V,Q) via universal property
- [ ] Prove this action satisfies the Clifford relation: a(v) ∘ a(v) = Q(v) · id
  - [x] In the transported hyperbolic case, prove the vector relation on `⋀W`
- [ ] Prove ⋀W is a faithful Cl(V,Q)-module (for non-degenerate Q)
  - [x] In the split model, show `splitCliffordAction : Cl(W* × W, dualProd) → End(⋀W)` is
    surjective and injective
  - [x] Transport that faithfulness to explicit hyperbolic presentations `Q ≃ dualProd K W`,
    the Witt-presentation API, and the split-rank canonical Witt model

### 2.3 The Spinor Module
- [ ] **Define `SpinorModule Q` := ⋀W as a `Module (CliffordAlgebra Q)`**
- [ ] Prove irreducibility (for algebraically closed fields, even dimension)
  - [x] In the split model, prove the full Clifford module `⋀W` is simple
  - [x] Transport that simplicity to the explicit hyperbolic, Witt, and split-Witt presentation APIs
- [ ] Prove the dimension formula: dim(S) = 2^(n/2)
  - [x] In the explicit hyperbolic case `Q ≃ dualProd K W`, show `dim(⋀W) = 2 ^ (dim V / 2)`

---

## Phase 3: Spin Group Action (Week 4-5)

### 3.1 Restriction to Spin Group
- [x] Show `spinGroup Q` acts on `SpinorModule Q` by restriction of Clifford action
- [x] This gives the **spin representation**: `spinGroup Q →* (SpinorModule Q →ₗ SpinorModule Q)`
- [x] Prove this is a group homomorphism

### 3.2 Half-Spin / Chiral Representations (even dimension)
- [x] Use the ℤ/2-grading of Cl(V,Q) to decompose S = S⁺ ⊕ S⁻
- [x] Define the chosen-model splitting `⋀W = ⋀^even W ⊕ ⋀^odd W`
- [x] Identify the zero-form chiral pieces on the chosen `⋀W` model with `⋀^even W` and `⋀^odd W`
- [x] Package the chosen-model positive/negative chiral halves and their restricted spin
  representations through the hyperbolic/Witt presentation APIs
- [x] Prove the split hyperbolic spin action on the chosen `⋀W` model preserves `⋀^even W` and `⋀^odd W`
- [x] In positive split rank, prove the chosen even and odd halves have equal dimension
- [ ] Identify these chosen even/odd summands with the ambient chiral modules `S⁺` and `S⁻`
- [x] Prove Spin(V,Q) preserves the decomposition (Weyl spinors)
- [ ] Prove S⁺ and S⁻ are irreducible and inequivalent (for dim ≥ 4)
  - [x] In the split model, prove `⋀^even W` is simple under the even Clifford algebra and, in
    positive split rank, prove the same for `⋀^odd W`
  - [x] Transport that half-spin simplicity to the explicit hyperbolic, Witt, and split-Witt
    presentation APIs
  - [x] Prove the chosen-model inequivalence statement and transport it to the explicit
    hyperbolic, Witt, and split-Witt presentation APIs
  - [ ] Prove the remaining ambient/global `S⁺` / `S⁻` version

---

## Phase 4: Key Theorems (Week 5-7)

### 4.1 Periodicity & Classification
- [ ] Cl(n, ℂ) ≅ Mat(2^(n/2), ℂ) for n even
- [ ] Cl(n, ℂ) ≅ Mat(2^((n-1)/2), ℂ) × Mat(2^((n-1)/2), ℂ) for n odd
- [ ] Bott periodicity for real Clifford algebras (period 8)

### 4.2 Low-Dimensional Examples
- [ ] Spin(2) → U(1) (circle)
- [ ] Spin(3) → SU(2) (Pauli matrices / quaternions)
- [ ] Spin(4) → SU(2) × SU(2)
- [ ] These connect spinors to familiar physics

### 4.3 The Covering Map
- [ ] Spin(V,Q) → SO(V,Q) is a double cover
- [ ] Kernel is {1, -1}
- [ ] The spin representation does NOT factor through SO

---

## Phase 5: Paper & Polish (Week 7-8)

### 5.1 Paper Writing
- [ ] Introduction: why spinors matter, why formalization is novel
- [ ] Related work: lean-ga, Mathlib Clifford, what's missing
- [ ] Formalization architecture
- [ ] Key proof highlights (the hard parts)
- [ ] Lessons learned & Mathlib gaps discovered
- [ ] Future work: spinor bundles, Dirac operators

### 5.2 Code Quality
- [x] Full `lake build` clean
- [x] Zero `sorry` / `admit` sweep
- [ ] Mathlib-compatible style
- [ ] Module documentation

### 5.3 Submission
- [ ] Target: CPP 2027 (deadline ~Sep 2026) or ITP 2027
- [ ] Secondary: *Advances in Applied Clifford Algebras* (journal, no deadline)
- [ ] Tertiary: *Journal of Automated Reasoning*

---

## Dependencies (from Mathlib)

| What we need | Mathlib status | Notes |
|---|---|---|
| `CliffordAlgebra Q` | ✅ Complete | Universal property, lift, grading |
| `ExteriorAlgebra R M` | ✅ Complete | As quotient of tensor algebra |
| `spinGroup Q` | ✅ Basic | Group structure, conjugation action |
| `pinGroup Q` | ✅ Basic | Same |
| `QuadraticForm.Isotropic` | ⚠️ Partial | May need maximal isotropic API |
| `QuadraticForm.WittDecomp` | ❌ Missing | Need to build this |
| Interior product on ⋀V | ⚠️ Partial | `ExteriorAlgebra.ιMulti` exists, contraction unclear |
| Clifford module structure | ❌ Missing | **This is the main contribution** |

---

## Non-Goals
- Spinor bundles / differential geometry (Mathlib's manifold library too immature)
- Dirac operators (requires spinor bundles)
- Computational paths (this is standard Mathlib-style formalization)
- Physics applications (pure algebra focus)
