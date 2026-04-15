# SpinorLean

First-ever formalization of spinor representations from Clifford algebras in Lean 4 / Mathlib.

## What This Is

The **spinor representation** is one of the most important constructions in mathematics and physics — it's how the Spin group acts on "square roots of geometry." Despite Clifford algebras and Spin groups already existing in Mathlib, nobody has formalized the actual spinor module that connects them.

This project fills that gap.

## Structure

```
SpinorLean/
├── Spinor/
│   ├── Basic.lean          -- Core spinor module definition
│   ├── Isotropic.lean      -- Maximal isotropic subspaces
│   ├── WittDecomp.lean     -- Witt decomposition V ≅ W ⊕ W* ⊕ V₀
│   ├── CliffordAction.lean -- Cl(V,Q) acts on ⋀W
│   ├── SpinRep.lean        -- Spin group representation
│   ├── Chiral.lean         -- Half-spin representations S⁺, S⁻
│   ├── Periodicity.lean    -- Clifford algebra classification
│   └── Examples/
│       ├── Spin2.lean      -- Spin(2) → U(1)
│       ├── Spin3.lean      -- Spin(3) → SU(2)
│       └── Spin4.lean      -- Spin(4) → SU(2) × SU(2)
├── ROADMAP.md
├── AGENTS.md
└── lakefile.lean
```

## Building

```bash
lake build
```

## References

- Lawson, Michelson — *Spin Geometry* (Princeton, 1989)
- Chevalley — *The Algebraic Theory of Spinors and Clifford Algebras* (Springer, 1996)
- Atiyah, Bott, Shapiro — *Clifford Modules* (Topology, 1964)

## Status

🚧 Under construction. See [ROADMAP.md](ROADMAP.md) for progress.
