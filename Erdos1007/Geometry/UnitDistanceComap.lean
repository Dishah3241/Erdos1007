/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Unit-distance representations pull back along injective homomorphisms

A unit-distance representation of a graph in `ℝⁿ` is an injective placement of its vertices in
which every edge is a segment of length one. Precomposing such a placement with an injective graph
homomorphism represents the domain graph. The same conclusion for a spanning subgraph `H ≤ G`,
and for a graph embedding `H ↪g G`, follows at once.

This is blueprint node `lem:monotone`: dimension is monotone under taking subgraphs, in the form
that a representation of `G` in `ℝⁿ` yields one of any graph mapped injectively into `G`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 4, attributed there to Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

namespace Erdos1007

open SimpleGraph

@[expose] public section

/-- A unit-distance representation of `G` in `ℝⁿ` pulls back along an injective homomorphism
`φ : H →g G` (blueprint node `lem:monotone`).

The placement of `H` is the placement of `G` precomposed with `φ`. Injectivity of both maps keeps
the placement injective, and `φ` sends edges of `H` to edges of `G`. Chaffee–Noble Lemma 4,
attributed there to Erdős–Harary–Tutte. -/
theorem unitDistance_comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H →g G) (hφ : Function.Injective φ) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 := by
  rintro ⟨f, hfInj, hfDist⟩
  refine ⟨fun w => f (φ w), hfInj.comp hφ, ?_⟩
  intro u v huv
  exact hfDist (φ u) (φ v) (φ.map_adj huv)

/-- A unit-distance representation of `G` restricts to any spanning subgraph `H ≤ G` on the same
vertex type (blueprint node `lem:monotone`; Chaffee–Noble Lemma 4). -/
theorem unitDistance_of_le {V : Type*} {G H : SimpleGraph V} {n : ℕ} (hHG : H ≤ G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 :=
  unitDistance_comap (Hom.ofLE hHG) Function.injective_id

/-- A unit-distance representation of `G` pulls back along a graph embedding `H ↪g G`
(blueprint node `lem:monotone`; Chaffee–Noble Lemma 4). -/
theorem unitDistance_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H ↪g G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 :=
  unitDistance_comap φ.toHom φ.injective

end

end Erdos1007
