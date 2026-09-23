/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

/-!
# Nine edges on five vertices

A simple graph on five vertices with nine edges is the complete graph with one edge deleted.
Nine edges force every degree to be at least three: a vertex of degree at most two leaves at
most six edges on the other four vertices, and six plus two is eight. The degree sum is then
eighteen, so the degrees are three `4`s and two `3`s. A vertex of degree four is adjacent to
every other vertex, so the complement is the single edge joining the two vertices of degree
three.

## Source

Chaffee and Noble, Australas. J. Combin. **64(2)** (2016), 327–333, Theorem 7, assert that on
five vertices the degree sequence `(4, 4, 4, 3, 3)` corresponds solely to the complete graph
with one edge deleted.
-/

namespace Erdos1007

open Finset SimpleGraph

/-- On `Fin 5` every degree is strictly less than five, so a lower bound of three leaves only
`3` and `4`. -/
private lemma degree_eq_three_or_four {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v) (v : Fin 5) : G.degree v = 3 ∨ G.degree v = 4 := by
  have hlt : G.degree v < 5 := by simpa [Fintype.card_fin] using G.degree_lt_card_verts v
  have h3 : 3 ≤ G.degree v := hdeg v
  omega

/-- Nine edges give degree sum eighteen. With every degree equal to `3` or `4`, exactly two
vertices have degree three. -/
private lemma card_degree_eq_three {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    #(univ.filter fun v : Fin 5 => G.degree v = 3) = 2 := by
  set s : Finset (Fin 5) := univ.filter fun v => G.degree v = 3
  have hs3 : ∀ v ∈ s, G.degree v = 3 := fun v hv => (mem_filter.mp hv).2
  have hs4 : ∀ v ∈ sᶜ, G.degree v = 4 := by
    intro v hv
    have hne : G.degree v ≠ 3 := by
      rw [mem_compl] at hv
      intro h
      exact hv (mem_filter.mpr ⟨mem_univ v, h⟩)
    rcases degree_eq_three_or_four hdeg v with h | h
    · exact absurd h hne
    · exact h
  have hsum : ∑ v, G.degree v = #s * 3 + #sᶜ * 4 := by
    rw [← sum_add_sum_compl s, sum_const_nat hs3, sum_const_nat hs4]
  have htot : ∑ v, G.degree v = 18 := by
    simpa [hE] using G.sum_degrees_eq_twice_card_edges
  have hc : #sᶜ = 5 - #s := by rw [card_compl, Fintype.card_fin]
  have hnum : #s * 3 + (5 - #s) * 4 = 18 := by rw [← hc, ← hsum, htot]
  have hle : #s ≤ 5 := by simpa [card_univ, Fintype.card_fin] using s.card_le_univ
  omega

/-- Nine edges on `Fin 5` force every degree to be at least three. A vertex of degree at most
two meets at most two edges, and the other four vertices span at most `Nat.choose 4 2 = 6`
edges, so the graph would have at most eight edges. -/
private lemma degree_ge_three_of_nine_edges {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (v : Fin 5) : 3 ≤ G.degree v := by
  rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
  · have hdeg : G.degree v ≤ 2 := Nat.lt_succ_iff.mp hlt
    have hcard4 : Fintype.card {w : Fin 5 // w ≠ v} = 4 := by
      rw [Fintype.card_subtype_compl (fun w => w = v), Fintype.card_subtype_eq,
        Fintype.card_fin]
    have hrest : (G.induce {w | w ≠ v}).edgeFinset.card ≤ 6 := by
      calc
        (G.induce {w | w ≠ v}).edgeFinset.card
            ≤ (Fintype.card {w : Fin 5 // w ≠ v}).choose 2 :=
          (G.induce {w | w ≠ v}).card_edgeFinset_le_card_choose_two
        _ = Nat.choose 4 2 := by rw [hcard4]
        _ = 6 := by decide
    have hrestEq : (G.induce {w | w ≠ v}).edgeFinset.card =
        G.edgeFinset.card - G.degree v := by
      rw [← G.card_edgeFinset_deleteIncidenceSet v,
        ← G.card_edgeFinset_induce_compl_singleton v]
      rfl
    have hdegCard : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
    have hle : G.edgeFinset.card ≤ 8 := by
      have hsum : G.edgeFinset.card =
          (G.induce {w | w ≠ v}).edgeFinset.card + G.degree v := by omega
      omega
    omega
  · exact hge

/-- The complement is the edge joining the two vertices of degree three. -/
private lemma compl_eq_edge {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    ∃ a b : Fin 5, a ≠ b ∧ Gᶜ = edge a b := by
  obtain ⟨a, b, hab, hs⟩ := card_eq_two.mp (card_degree_eq_three hE hdeg)
  have ha : G.degree a = 3 := by
    have : a ∈ univ.filter fun v => G.degree v = 3 := by rw [hs]; simp
    exact (mem_filter.mp this).2
  have hdeg4 : ∀ v, v ≠ a → v ≠ b → G.degree v = 4 := by
    intro v hva hvb
    have hv : v ∉ univ.filter fun w => G.degree w = 3 := by
      rw [hs]
      simp [hva, hvb]
    have hne : G.degree v ≠ 3 := fun h => hv (mem_filter.mpr ⟨mem_univ v, h⟩)
    rcases degree_eq_three_or_four hdeg v with h | h
    · exact absurd h hne
    · exact h
  have huniv : ∀ v, v ≠ a → v ≠ b → G.IsUniversal v := by
    intro v hva hvb
    exact (G.degree_eq_card_sub_one v).mp <| by
      simpa [Fintype.card_fin] using hdeg4 v hva hvb
  have hsub : univ \ {a, b} ⊆ G.neighborFinset a := by
    intro w hw
    obtain ⟨-, hwab⟩ := mem_sdiff.mp hw
    simp only [mem_insert, mem_singleton, not_or] at hwab
    obtain ⟨hwa, hwb⟩ := hwab
    rw [mem_neighborFinset]
    exact ((huniv w hwa hwb) hwa).symm
  have hpair : #({a, b} : Finset (Fin 5)) = 2 := by
    rw [card_insert_of_notMem (by simpa using hab), card_singleton]
  have hcard3 : #(univ \ ({a, b} : Finset (Fin 5))) = 3 := by
    rw [card_sdiff, card_univ, Fintype.card_fin, inter_univ, hpair]
  have hNa : univ \ {a, b} = G.neighborFinset a :=
    eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, ha, hcard3])
  have hnot : ¬ G.Adj a b := by
    intro hab'
    have hbmem : b ∈ G.neighborFinset a := by rwa [mem_neighborFinset]
    rw [← hNa] at hbmem
    exact (mem_sdiff.mp hbmem).2 (by simp)
  -- Every pair other than `{a, b}` is an edge, so the complement is exactly `edge a b`.
  have hadj_iff : ∀ u v, G.Adj u v ↔ u ≠ v ∧ s(u, v) ≠ s(a, b) := by
    intro u v
    constructor
    · intro huv
      refine ⟨huv.ne, ?_⟩
      intro hsuv
      rw [Sym2.eq_iff] at hsuv
      rcases hsuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnot huv
      · exact hnot huv.symm
    · rintro ⟨hne, hsuv⟩
      by_cases hua : u = a
      · subst hua
        have hvb : v ≠ b := by
          rintro rfl
          exact hsuv rfl
        exact ((huniv v hne.symm hvb) hne.symm).symm
      · by_cases hub : u = b
        · subst hub
          have hva : v ≠ a := by
            rintro rfl
            exact hsuv Sym2.eq_swap
          exact ((huniv v hva hne.symm) hne.symm).symm
        · exact huniv u hua hub hne
  refine ⟨a, b, hab, ?_⟩
  ext u v
  simp only [compl_adj, edge_adj]
  constructor
  · intro ⟨hne, hnadj⟩
    have hsuv : s(u, v) = s(a, b) := by
      by_contra hne'
      exact hnadj ((hadj_iff u v).mpr ⟨hne, hne'⟩)
    rw [Sym2.eq_iff] at hsuv
    exact ⟨hsuv, hne⟩
  · rintro ⟨hsuv, hne⟩
    refine ⟨hne, ?_⟩
    intro hadj
    exact ((hadj_iff u v).mp hadj).2 (Sym2.eq_iff.mpr hsuv)

@[expose] public section

/-- A simple graph on five vertices with nine edges is the complete graph with one edge deleted.

Nine edges force every degree to be at least three. The degree sum is then eighteen, so the
degrees are three `4`s and two `3`s; each degree-`4` vertex is adjacent to every other vertex,
and the complement is the edge joining the two degree-`3` vertices.

Chaffee and Noble assert that the degree sequence `(4, 4, 4, 3, 3)` corresponds solely to this
graph, in the proof of their Theorem 7. -/
theorem nine_edges_iso_deleteEdge
    {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) :
    ∃ a b : Fin 5, a ≠ b ∧
      Nonempty (G ≃g (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)}) := by
  have hdeg : ∀ v, 3 ≤ G.degree v := fun v => degree_ge_three_of_nine_edges hE v
  obtain ⟨a, b, hab, hcompl⟩ := compl_eq_edge hE hdeg
  have hG : G = (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)} := by
    rw [← compl_compl G, hcompl]
    simp [deleteEdges, edge]
  exact ⟨a, b, hab, Nonempty.intro (hG ▸ (Iso.refl : G ≃g G))⟩

end

end Erdos1007
