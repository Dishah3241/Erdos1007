/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Erdos1007.Combinatorics.SimpleGraph.TwoRegularSix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Six vertices, nine edges, minimum degree three

On six vertices, nine edges and minimum degree three give degree sum eighteen, so the graph is
three-regular and its complement is two-regular. A two-regular graph on six vertices is the
hexagon `C₆` or the disjoint sum of two triangles, and the complement of that disjoint sum is
the complete bipartite graph `K₃,₃`.
-/

namespace Erdos1007

open SimpleGraph

/-- Nine edges and minimum degree three on six vertices force the graph to be three-regular. -/
private lemma isRegularOfDegree_three_of_nine_edges
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    G.IsRegularOfDegree 3 := by
  have hdegSum : ∑ v, G.degree v = 18 := by
    rw [G.sum_degrees_eq_twice_card_edges, hE]
  have hthree : ∑ v : Fin 6, (3 : ℕ) = 18 := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
  have hle : ∀ v ∈ Finset.univ, (3 : ℕ) ≤ G.degree v := fun v _ => hdeg v
  intro v
  have hv :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (hthree.trans hdegSum.symm) v (Finset.mem_univ v)
  exact hv.symm

/-- The complement of two disjoint copies of `K₃` is `K₃,₃`. -/
private lemma compl_sum_top_eq_completeBipartiteGraph :
    ((⊤ : SimpleGraph (Fin 3)) ⊕g (⊤ : SimpleGraph (Fin 3)))ᶜ =
      completeBipartiteGraph (Fin 3) (Fin 3) := by
  ext u v
  rcases u with a | a <;> rcases v with b | b
  · simp [compl_adj, top_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, top_adj, completeBipartiteGraph_adj]

/-- An isomorphism `Gᶜ ≃g H` is an isomorphism `G ≃g Hᶜ` on the same vertex equivalence. -/
private def isoOfComplIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Gᶜ ≃g H) : G ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' {a b} := by
    rw [compl_adj, e.toEquiv.injective.ne_iff, not_congr e.map_rel_iff', ← compl_adj,
      compl_compl]

/-- Equal simple graphs on one vertex type are isomorphic via the identity. -/
private def isoOfEq {V : Type*} {G H : SimpleGraph V} (h : G = H) : G ≃g H where
  toEquiv := Equiv.refl V
  map_rel_iff' := by
    subst h
    intro a b
    rfl

@[expose] public section

/-- A simple graph on six vertices with nine edges and minimum degree three is isomorphic
to `K₃,₃`, or its complement is the hexagon `C₆`. -/
theorem nine_edges_six_minDegree_three
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (Gᶜ ≃g cycleGraph 6) := by
  have hreg : G.IsRegularOfDegree 3 :=
    isRegularOfDegree_three_of_nine_edges hE hdeg
  have hcomplDeg : Gᶜ.IsRegularOfDegree (Fintype.card (Fin 6) - 1 - 3) :=
    IsRegularOfDegree.compl hreg
  have htwo : Fintype.card (Fin 6) - 1 - 3 = 2 := by rw [Fintype.card_fin]
  have hcompl : Gᶜ.IsRegularOfDegree 2 := htwo ▸ hcomplDeg
  rcases isRegularOfDegree_two_fin_six Gᶜ hcompl with hC | hT
  · exact Or.inr hC
  · obtain ⟨e⟩ := hT
    exact Or.inl ⟨Iso.comp (isoOfEq compl_sum_top_eq_completeBipartiteGraph)
      (isoOfComplIso e)⟩

end

end Erdos1007
