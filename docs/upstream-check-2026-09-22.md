# Upstream type check, 2026-09-22

This record shows that the proof proves `formal-conjectures`' own declaration. It is checked against
the upstream declaration itself, not only against a copy of its statement. That is items 2 to 4 of
`formal-conjectures`' `PROOFS.md` link checklist, done by the kernel.

- **`formal-conjectures`** at `2a46c7bd74505b85f4967475bb733ded0ef8d348`, built with
  `lake build 'FormalConjectures.ErdosProblems.«1007»'`.
- **This repository** with the Lean sources of commit `2a8b97d`, the last commit to change them,
  built with `lake build`.
- Both pin Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, so their
  compiled modules load into one environment.

## The check

```lean
import FormalConjectures.ErdosProblems.«1007»
import Erdos1007.Standalone.Mathlib.InlineErdos1007Proof

/-- The proof, elaborated against the type of upstream's declaration. -/
theorem upstream_dimension_four_extremal_holds :
    type_of% @Erdos1007.erdos_1007.variants.dimension_four_extremal :=
  Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.proof

/-- The inlined statement and upstream's declaration type are the same proposition. -/
example : Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal =
    type_of% @Erdos1007.erdos_1007.variants.dimension_four_extremal := rfl

#check @Erdos1007.erdos_1007.variants.dimension_four_extremal
#print axioms upstream_dimension_four_extremal_holds
```

Upstream's file opens `namespace Erdos1007`, so its declaration's full name is
`Erdos1007.erdos_1007.variants.dimension_four_extremal`. This repository's declarations live under
`Erdos1007.Standalone` and `Erdos1007.Palomar`, and no name collides.

## Command

Run from the `formal-conjectures` checkout, with this repository at `$E`:

```sh
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$E/.lake/build/lib/lean\" lean Check.lean"
```

## Result

```text
Erdos1007.erdos_1007.variants.dimension_four_extremal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.HasDimension 4 →
    G.edgeSet.ncard = 9 → (∀ (v : Fin n), ∃ w, G.Adj v w) → Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
'upstream_dimension_four_extremal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
