/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Unit-distance graphs of dimension four with nine edges

A graph has *dimension* `n` when `n` is least such that its vertices can be placed injectively in
`ℝⁿ` with every edge realised as a unit segment. House proved that a graph of dimension four has
at least nine edges, and that nine is attained only by `K₃,₃`. This file states that extremal
half.

`Challenge.lean` is generated from this file; see `AGENTS.md`. Everything here rests on Mathlib
alone, so a reader can check the statement without following a definition elsewhere.

## Source

The statement is the `erdos_1007.variants.dimension_four_extremal` declaration of
[google-deepmind/formal-conjectures][fc], reproduced with its definitions inlined and no change of
meaning. The proof of record is Chaffee and Noble, *Dimension 4 and dimension 5 graphs with
minimum edge set*, Australas. J. Combin. **64(2)** (2016), 327–333, Theorem 7, which is open
access; the original is House, *A 4-dimensional graph has at least 9 edges*, Discrete Math.
**313(18)** (2013), 1783–1789.

[fc]: https://github.com/google-deepmind/formal-conjectures
-/

@[expose] public section

namespace Erdos1007.Standalone.Mathlib.InlineErdos1007

open scoped RealInnerProductSpace

/-- `G` admits a unit-distance representation in `ℝⁿ`: an injective placement of its vertices
sending every **edge** to a pair of points at distance one.

Non-adjacent vertices are unconstrained, so this is a unit-distance *representation* and not the
stricter notion of a unit-distance *graph*, where distance one would force adjacency. The informal
claim asks only that every edge be a unit segment, so the weaker reading is the faithful one;
`UnitDistanceEmbeddable.separating` exhibits the difference. -/
def UnitDistanceEmbeddable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
    ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/-- Separating example for `UnitDistanceEmbeddable`, required by `lake exe fidelity`.

The nearest plausible wrong definition adds `∀ u v, dist (f u) (f v) = 1 → G.Adj u v`, turning a
representation into a unit-distance graph. This exhibits a placement that satisfies the definition
as written while putting a **non-edge** at distance one, so the definition demonstrably does not
constrain non-adjacent vertices. Without it a development could silently prove the stricter
theorem, which is a different and stronger claim than the source makes.

An edge plus a third vertex in `ℝ¹` does it: send the edge to `0, 1` and the third vertex to `2`.
Every edge is a unit segment and the non-edge between the second and third vertices is also a unit
segment.

An earlier version of this asserted instead that **no** placement satisfies the stricter reading.
That was wrong, and an adversarial review kernel-checked the refutation: placing the third vertex
at `3` instead satisfies the stricter reading too. Non-existence of a strict placement is a much
stronger and harder claim, and it is not what separating the definitions requires. -/
def UnitDistanceEmbeddable.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V) (n : ℕ) (f : V → EuclideanSpace ℝ (Fin n)),
    Function.Injective f ∧ (∀ u v : V, G.Adj u v → dist (f u) (f v) = 1) ∧
      ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v ∧ dist (f u) (f v) = 1

/-- `G` has dimension `n`: the least `m` admitting a unit-distance representation of `G` in `ℝᵐ`.

`IsLeast` carries both halves — `G` is representable in `ℝⁿ`, and in no smaller space. Weakening
this to mere representability in `ℝⁿ` would make the theorem below false, since a graph
representable in `ℝ⁴` may have dimension less than four. -/
def HasDimension {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  IsLeast {m | UnitDistanceEmbeddable G m} n

/-- Separating example for `HasDimension`, required by `lake exe fidelity`.

The nearest plausible wrong definition is membership in place of leastness: `G` is representable
in `ℝⁿ`. This asserts a graph representable in `ℝ⁴` that does not have dimension four, separating
the two.

The edge is required because without it the empty graph satisfies this degenerately — it is
representable in every dimension and has dimension zero — which an adversarial review
kernel-checked. A separating example that only the empty object witnesses establishes nothing
about the definition, so this demands a graph with an edge. `K₂` is the intended witness:
representable in `ℝ⁴`, of dimension one. -/
def HasDimension.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    (∃ u v : V, G.Adj u v) ∧ UnitDistanceEmbeddable G 4 ∧ ¬ HasDimension G 4

/-- **Erdős problem 1007, extremal half.** A graph of dimension four with nine edges and no
isolated vertex is `K₃,₃`.

The hypothesis that every vertex has a neighbour is not decoration: without it the conclusion is
false, since adjoining isolated vertices to `K₃,₃` changes neither the dimension nor the edge
count while destroying the isomorphism. -/
def DimensionFourExtremal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasDimension G 4 → G.edgeSet.ncard = 9 → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
      Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))

/-- Satisfiability witness for `DimensionFourExtremal`, required by `lake exe fidelity`.

A universally quantified claim whose hypotheses no object satisfies is vacuously true, and vacuous
truth passes `lake build`, `lake exe axioms`, and Comparator alike. This asserts that some graph
meets all three hypotheses at once.

Discharging it is real mathematics, not a formality: it amounts to showing that `K₃,₃` has
dimension exactly four, which is half of what the source paper proves. That the anti-vacuity
obligation is this expensive is itself the finding — the theorem says nothing at all unless such a
graph exists. -/
def DimensionFourExtremal.witness : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasDimension G 4 ∧ G.edgeSet.ncard = 9 ∧ ∀ v : Fin n, ∃ w : Fin n, G.Adj v w

end Erdos1007.Standalone.Mathlib.InlineErdos1007

/-!
## Formal proof

Proved in `InlineErdos1007Proof`.

* `separating` → `separating.proof`
* `HasDimension` → `HasDimension.proof`
* `DimensionFourExtremal` → `DimensionFourExtremal.proof`
* `witness` → `witness.proof`
-/
