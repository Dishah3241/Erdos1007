/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Erdos1007.Geometry.EightEdges
import Erdos1007.Geometry.Reattach
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Nine edges and a vertex of degree one or two

A finite graph with nine edges and a vertex of degree one or two admits an injective placement
of its vertices in `ℝ³` in which every edge is a segment of length one.

## References

Chaffee and Noble, Australas. J. Combin. **64(2)** (2016), 327–333, the argument of Theorem 7.
Blueprint node `lem:min-degree`.
-/

namespace Erdos1007

open SimpleGraph Metric

/-- Deleting `u` removes exactly `G.degree u` edges. -/
private lemma card_edgeFinset_induce_ne {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (u : V) :
    (G.induce {v | v ≠ u}).edgeFinset.card = G.edgeFinset.card - G.degree u := by
  rw [← G.card_edgeFinset_deleteIncidenceSet u,
    ← G.card_edgeFinset_induce_compl_singleton u]
  rfl

@[expose] public section

-- `fintypeEdgeSetSup` is not definitionally the `edgeFinset` instance used for `G' ⊔ E`.
-- `DecidableEq V` names the two neighbours. The type of `edgeFinset` does not use it.
set_option linter.unusedDecidableInType false in
attribute [-instance] SimpleGraph.fintypeEdgeSetSup in
/-- A finite graph with nine edges and a vertex of degree one or two admits an injective
placement in `ℝ³` in which every edge has length one (blueprint node `lem:min-degree`).

The induced subgraph on `V \ {u}` has `9 - G.degree u` edges. Degree one leaves eight. Degree
two leaves seven, and the edge between the two neighbours brings the count to at most eight.
`unitDistance_of_edgeFinset_card_le_eight` places that graph, and
`unitDistance_extend_degree_le_two` restores `u`. The hypothesis `0 < G.degree u` keeps the
degree equal to one or two: an isolated vertex leaves all nine edges on `V \ {u}`.

Chaffee–Noble, the argument of Theorem 7. -/
theorem unitDistance_of_nine_edges_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) {u : V} (hdeg : G.degree u ≤ 2)
    (hpos : 0 < G.degree u) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
  have glue (H : SimpleGraph {v // v ≠ u}) [DecidableRel H.Adj]
      (hsub : ∀ ⦃a b : {v // v ≠ u}⦄,
        (G.induce {v | v ≠ u}).Adj a b → H.Adj a b)
      (hextra : ∀ ⦃a b : {v // v ≠ u}⦄, G.degree u = 2 → a.1 ∈ G.neighborSet u →
        b.1 ∈ G.neighborSet u → a ≠ b → H.Adj a b)
      (hEle : H.edgeFinset.card ≤ 8) :
      ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
        ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
    obtain ⟨f, hfInj, hfDist⟩ := unitDistance_of_edgeFinset_card_le_eight (G := H) hEle
    refine unitDistance_extend_degree_le_two hdeg ⟨f, hfInj, ?_⟩
    intro a b hcond
    rcases hcond with hadj | ⟨h2, haN, hbN, hab⟩
    · exact hfDist a b (hsub hadj)
    · exact hfDist a b (hextra h2 haN hbN hab)
  obtain h1 | h2 : G.degree u = 1 ∨ G.degree u = 2 := by omega
  · let H : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hEle : H.edgeFinset.card ≤ 8 := by
      rw [card_edgeFinset_induce_ne (G := G) u]
      omega
    exact glue H (fun _ _ h => h) (fun _ _ h2 _ _ _ => by omega) hEle
  · let G' : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hNcard : (G.neighborFinset u).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, h2]
    obtain ⟨a, b, _, hN⟩ := Finset.card_eq_two.mp hNcard
    have ha : G.Adj u a := (G.mem_neighborFinset u a).mp (by simp [hN])
    have hb : G.Adj u b := (G.mem_neighborFinset u b).mp (by simp [hN])
    let a' : {v // v ≠ u} := ⟨a, ha.ne'⟩
    let b' : {v // v ≠ u} := ⟨b, hb.ne'⟩
    let E : SimpleGraph {v // v ≠ u} := fromRel fun x y => x = a' ∧ y = b'
    let H : SimpleGraph {v // v ≠ u} := G' ⊔ E
    have hHcard : H.edgeFinset.card ≤ G'.edgeFinset.card + 1 := by
      have hsub : H.edgeFinset ⊆ G'.edgeFinset ∪ {s(a', b')} := by
        intro e he
        have heSet : e ∈ H.edgeSet := (mem_edgeFinset (G := H)).mp he
        induction e using Sym2.ind with
        | h x y =>
          have hadj : H.Adj x y := (mem_edgeSet (G := H)).mp heSet
          simp only [H, sup_adj] at hadj
          rcases hadj with hG | ⟨_, hpair⟩
          · exact Finset.mem_union_left _ ((mem_edgeFinset (G := G')).mpr
              ((mem_edgeSet (G := G')).mpr hG))
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · rw [Sym2.eq_swap]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hunion : (G'.edgeFinset ∪ {s(a', b')}).card ≤ G'.edgeFinset.card + 1 := by
        exact (Finset.card_union_le _ _).trans (by simp)
      exact (Finset.card_le_card hsub).trans hunion
    have hEle : H.edgeFinset.card ≤ 8 := by
      have hG' : G'.edgeFinset.card = G.edgeFinset.card - 2 := by
        rw [card_edgeFinset_induce_ne (G := G) u, h2]
      omega
    exact glue H (fun _ _ h => (le_sup_left : G' ≤ H) h)
      (fun x y _ hxN hyN hxy => by
        have hxab : x.1 = a ∨ x.1 = b := by
          have hxFin : x.1 ∈ G.neighborFinset u :=
            (G.mem_neighborFinset u x.1).mpr ((G.mem_neighborSet u x.1).mp hxN)
          rw [hN] at hxFin
          simpa using hxFin
        have hyab : y.1 = a ∨ y.1 = b := by
          have hyFin : y.1 ∈ G.neighborFinset u :=
            (G.mem_neighborFinset u y.1).mpr ((G.mem_neighborSet u y.1).mp hyN)
          rw [hN] at hyFin
          simpa using hyFin
        have hEadj : E.Adj x y := by
          rw [fromRel_adj]
          refine ⟨hxy, ?_⟩
          rcases hxab with hxa | hxb <;> rcases hyab with hya | hyb
          · exact absurd (Subtype.ext (hxa.trans hya.symm)) hxy
          · exact Or.inl ⟨Subtype.ext hxa, Subtype.ext hyb⟩
          · exact Or.inr ⟨Subtype.ext hya, Subtype.ext hxb⟩
          · exact absurd (Subtype.ext (hxb.trans hyb.symm)) hxy
        exact (le_sup_right : E ≤ H) hEadj)
      hEle

end

end Erdos1007
