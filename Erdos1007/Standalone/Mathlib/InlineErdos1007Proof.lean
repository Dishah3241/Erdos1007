/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007.Standalone.Mathlib.InlineErdos1007

import Erdos1007.Combinatorics.SimpleGraph.FiveVertices
import Erdos1007.Combinatorics.SimpleGraph.NineEdges
import Erdos1007.Combinatorics.SimpleGraph.SixVertices
import Erdos1007.Geometry.CompleteBipartite
import Erdos1007.Geometry.CompleteBipartiteLowerBound
import Erdos1007.Geometry.CompleteMinusEdge
import Erdos1007.Geometry.FinLe
import Erdos1007.Geometry.LowDegree
import Erdos1007.Geometry.Prism
import Erdos1007.Geometry.UnitDistanceComap
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Proofs for `InlineErdos1007`

The proof sibling. Unlike its statement module this may import the development, and it is the one
explicit exception to the standalone isolation rule.

`DimensionFourExtremal.proof`, its witness, and the three hypothesis-drop counterexamples are
discharged here. `Challenge.lean` still contains the advertised Palomar hole.
-/

public section

namespace Erdos1007.Standalone.Mathlib.InlineErdos1007

open SimpleGraph

/-- `K₂` plus an isolated vertex, placed in `ℝ¹`, has a non-edge at distance one. -/
theorem UnitDistanceEmbeddable.separating.proof : UnitDistanceEmbeddable.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have inj : Function.Injective (fun j : Fin 3 =>
      EuclideanSpace.single (0 : Fin 1) (j : ℝ)) := by
    intro u v h
    have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
    simp only [PiLp.single_eq_same] at hcoord
    exact Fin.ext (Nat.cast_inj.mp hcoord)
  let f : Fin 3 → EuclideanSpace ℝ (Fin 1) := fun j => EuclideanSpace.single 0 (j : ℝ)
  refine ⟨Fin 3, fromEdgeSet {s(0, 1)}, 1, f, ⟨f, inj, ?_⟩, inj, ?_, 1, 2, ?_, ?_, ?_⟩
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · decide
  · rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    decide
  · rw [dist_axis]
    norm_num

/-- A graph representable in `ℝ⁴` need not have dimension four. -/
theorem HasDimension.separating.proof : HasDimension.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have k2 (n : ℕ) (i : Fin n) : UnitDistanceEmbeddable (completeGraph (Fin 2)) n := by
    refine ⟨fun j => EuclideanSpace.single i (j : ℝ), ?_, ?_⟩
    · intro u v h
      have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin n) => p i) h
      simp only [PiLp.single_eq_same] at hcoord
      exact Fin.ext (Nat.cast_inj.mp hcoord)
    · intro u v huv
      fin_cases u <;> fin_cases v <;> rw [top_adj] at huv
      · exact (huv rfl).elim
      · rw [dist_axis]
        norm_num
      · rw [dist_axis]
        norm_num
      · exact (huv rfl).elim
  refine ⟨Fin 2, completeGraph (Fin 2), ⟨0, 1, ?_⟩, k2 4 0, ?_⟩
  · rw [top_adj]
    decide
  · intro h
    have hle : (4 : ℕ) ≤ 1 := (mem_lowerBounds.mp h.2) 1 (k2 1 0)
    exact absurd hle (by decide : ¬ (4 : ℕ) ≤ 1)

/-- `K₃,₃` has dimension four, nine edges, and no isolated vertex, so the extremal claim is not
vacuous. Half of the source paper's content. -/
theorem DimensionFourExtremal.witness.proof : DimensionFourExtremal.witness := by
  -- `K₃,₃` on `Fin 3 ⊕ Fin 3`, moved to `Fin 6` along the canonical bijection.
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let G : SimpleGraph (Fin 6) := K.map e
  let φ : K ≃g G := Iso.map e K
  have htransport {u w : Fin 3 ⊕ Fin 3} (hadj : K.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj
    rwa [Iso.map_apply e K u, Iso.map_apply e K w] at h
  have hpull {u w : Fin 6} (hadj : G.Adj u w) : K.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e K (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e K (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  refine ⟨6, G, ?_, ?_, ?_⟩
  · -- Representable in `ℝ⁴`, and in no `ℝᵐ` with `m ≤ 3`.
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfDist⟩ := completeBipartiteGraph_three_three_unitDistance
      refine ⟨fun x => f (e.symm x), hfInj.comp e.symm.injective, ?_⟩
      intro u v huv
      exact hfDist (e.symm u) (e.symm v) (hpull huv)
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g, hgInj, hgDist⟩ := hm
      have hKm :
          ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin m),
            Function.Injective f ∧ ∀ u v, K.Adj u v → dist (f u) (f v) = 1 :=
        ⟨fun x => g (e x), hgInj.comp e.injective,
          fun u v huv => hgDist (e u) (e v) (htransport huv)⟩
      have hmle : ¬ m ≤ 3 := fun hle =>
        not_exists_completeBipartiteGraph_three_three_unitDistance_three
          (unitDistance_of_fin_le hle hKm)
      exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
  · -- Nine edges: `K₃,₃` has `3 * 3` of them, and `φ` preserves the count.
    have hK : K.edgeSet.ncard = 9 := by
      rw [← ENat.natCast_inj, Set.coe_ncard_eq_encard K.edgeSet,
        encard_edgeSet_completeBipartiteGraph]
      simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      rw [← Nat.cast_mul]
    exact (Set.ncard_congr' φ.mapEdgeSet).symm.trans hK
  · -- Every vertex of `K₃,₃` has a neighbour, and `e` is bijective.
    intro v
    obtain ⟨w, hw⟩ : ∃ w, K.Adj (e.symm v) w := by
      cases e.symm v with
      | inl _ => exact ⟨Sum.inr 0, by simp [K]⟩
      | inr _ => exact ⟨Sum.inl 0, by simp [K]⟩
    exact ⟨e w, by simpa [e.apply_symm_apply] using htransport hw⟩

/-- **The target.** Chaffee–Noble, Australas. J. Combin. 64(2) (2016), Theorem 7. -/
theorem DimensionFourExtremal.proof : DimensionFourExtremal := by
  intro n G hdim hEdges hnbr
  -- Degree `0` has no neighbour. Degree `1` or `2` places the graph in `ℝ³`.
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcard : G.edgeFinset.card = 9 :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hEdges
  have noLow {m : ℕ} (hm : m ≤ 3)
      (hrep : ∃ f : Fin n → EuclideanSpace ℝ (Fin m), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) : False := by
    obtain ⟨g, hgInj, hgDist⟩ := unitDistance_of_fin_le hm hrep
    have h3 : UnitDistanceEmbeddable G 3 := ⟨g, hgInj, hgDist⟩
    have hle : (4 : ℕ) ≤ 3 := (mem_lowerBounds.mp hdim.2) 3 h3
    exact absurd hle (by decide : ¬ (4 : ℕ) ≤ 3)
  have hmin : ∀ v, 3 ≤ G.degree v := by
    intro v
    have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr (hnbr v)
    rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
    · have hle : G.degree v ≤ 2 := Nat.lt_succ_iff.mp hlt
      exact False.elim (noLow le_rfl
        (unitDistance_of_nine_edges_degree_le_two hcard hle hpos))
    · exact hge
  -- Nine edges and minimum degree three force five or six vertices.
  have hfive : 5 ≤ n := by
    simpa [Fintype.card_fin] using nine_edges_card_ge_five hcard
  have hsix : n ≤ 6 := by
    simpa [Fintype.card_fin] using nine_edges_minDegree_three_card_le_six hcard hmin
  have hn : n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl
  · -- Five vertices: `K₅` minus one edge, carried onto `s(3, 4)` and placed in `ℝ³`.
    obtain ⟨a, b, hab, ⟨φ⟩⟩ := nine_edges_degree_ge_three_iso_deleteEdge hcard hmin
    obtain ⟨e, hea, heb⟩ : ∃ e : Fin 5 ≃ Fin 5, e a = 3 ∧ e b = 4 := by
      let e1 : Fin 5 ≃ Fin 5 := Equiv.setValue (Equiv.refl (Fin 5)) a 3
      have he1 : e1 a = 3 := Equiv.setValue_eq (Equiv.refl (Fin 5)) a 3
      have hsym : a ≠ e1.symm (4 : Fin 5) := by
        intro hps
        have : e1 a = 4 := by
          rw [hps]
          exact e1.apply_symm_apply 4
        rw [he1] at this
        exact absurd this (by decide : (3 : Fin 5) ≠ 4)
      have hea' : Equiv.setValue e1 b 4 a = 3 := by
        unfold Equiv.setValue
        rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hab hsym]
        exact he1
      exact ⟨Equiv.setValue e1 b 4, hea', Equiv.setValue_eq e1 b 4⟩
    let ψ : (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)} ≃g
        (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} :=
      { __ := e
        map_rel_iff' := by
          intro u v
          simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hne, hnot⟩
            constructor
            · exact e.injective.ne_iff.mp hne
            · intro hs
              apply hnot
              rcases (Sym2.eq_iff).mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hea, heb]
              · rw [heb, hea]
                exact Sym2.eq_swap
          · rintro ⟨hne, hnot⟩
            constructor
            · exact e.injective.ne hne
            · intro hs
              apply hnot
              rcases (Sym2.eq_iff).mp hs with ⟨hu, hv⟩ | ⟨hu, hv⟩
              · have hu' : u = a := e.injective (hu.trans hea.symm)
                have hv' : v = b := e.injective (hv.trans heb.symm)
                rw [hu', hv']
              · have hu' : u = b := e.injective (hu.trans heb.symm)
                have hv' : v = a := e.injective (hv.trans hea.symm)
                rw [hu', hv']
                exact Sym2.eq_swap }
    exact False.elim (noLow le_rfl (unitDistance_of_embedding (Iso.comp ψ φ).toEmbedding
      completeGraph_five_deleteEdge_unitDistance))
  · -- Six vertices: `K₃,₃`, or the complement of `C₆`, which places in `ℝ²`.
    rcases nine_edges_six_minDegree_three hcard hmin with hK | hC
    · exact hK
    · obtain ⟨e⟩ := hC
      let ψ : G ≃g (cycleGraph 6)ᶜ :=
        { toEquiv := e.toEquiv
          map_rel_iff' := by
            intro u v
            simp only [RelIso.coe_fn_toEquiv]
            rw [compl_adj, e.map_adj_iff, (EquivLike.injective e).ne_iff]
            constructor
            · intro h
              rcases h with ⟨hne, hn⟩
              exact if hadj : G.Adj u v then hadj else
                absurd ((compl_adj G u v).mpr ⟨hne, hadj⟩) hn
            · intro hadj
              exact ⟨hadj.ne, fun hcompl => ((compl_adj G u v).mp hcompl).2 hadj⟩ }
      exact False.elim (noLow (by decide : (2 : ℕ) ≤ 3)
        (unitDistance_of_embedding ψ.toEmbedding compl_cycleGraph_six_unitDistance))

/-- `K₃,₃` has nine edges. -/
theorem completeBipartiteGraph_three_three_edgeSet_ncard :
    (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard = 9 := by
  rw [← ENat.natCast_inj,
    Set.coe_ncard_eq_encard (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet,
    encard_edgeSet_completeBipartiteGraph]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  rw [← Nat.cast_mul]

/-- Nine disjoint edges on `Fin 18` have nine edges and no isolated vertex, and are not `K₃,₃`. -/
theorem DimensionFourExtremal.drop_2.proof : DimensionFourExtremal.drop_2 := by
  intro hyp
  let P : SimpleGraph (Fin 9 × Fin 2) := {
    Adj := fun u v => u.1 = v.1 ∧ u.2 ≠ v.2
    symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun u h => h.2 rfl⟩
  }
  let e : Fin 9 × Fin 2 ≃ Fin 18 := finProdFinEquiv
  let G : SimpleGraph (Fin 18) := P.map e
  let φ : P ≃g G := Iso.map e P
  let : DecidableRel P.Adj := Classical.decRel P.Adj
  have hflip : ∀ b : Fin 2, b ≠ b + 1 := by decide
  have hother : ∀ b c : Fin 2, b ≠ c → c = b + 1 := by decide
  have hadj (u : Fin 9 × Fin 2) : P.Adj u (u.1, u.2 + 1) :=
    ⟨rfl, hflip u.2⟩
  have hdeg (u : Fin 9 × Fin 2) : P.degree u = 1 := by
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_eq_one.mpr ⟨(u.1, u.2 + 1), ?_⟩
    ext v
    simp only [mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨h1, hne⟩ := h
      exact Prod.ext h1.symm (hother u.2 v.2 hne)
    · rintro rfl
      exact hadj u
  have hsum : ∑ u : Fin 9 × Fin 2, P.degree u = 18 := by
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    norm_num
  have hP : P.edgeSet.ncard = 9 := by
    have htwice : ∑ u, P.degree u = 2 * P.edgeFinset.card :=
      P.sum_degrees_eq_twice_card_edges
    have hcard : P.edgeFinset.card = 9 := by
      rw [hsum] at htwice
      omega
    rw [Set.ncard_eq_toFinset_card' P.edgeSet]
    simpa [edgeFinset] using hcard
  have hG : G.edgeSet.ncard = 9 := (Set.ncard_congr' φ.mapEdgeSet).symm.trans hP
  have htransport {u w : Fin 9 × Fin 2} (hadj' : P.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj'
    rwa [Iso.map_apply e P u, Iso.map_apply e P w] at h
  have hnbr : ∀ v : Fin 18, ∃ w : Fin 18, G.Adj v w := by
    intro v
    refine ⟨e ((e.symm v).1, (e.symm v).2 + 1), ?_⟩
    simpa [e.apply_symm_apply] using htransport (hadj (e.symm v))
  have hnot : ¬ Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
    intro ⟨ψ⟩
    have hc := ψ.card_eq
    simp only [Fintype.card_fin, Fintype.card_sum] at hc
    omega
  exact hnot (hyp 18 G hG hnbr)

/-- `K₃,₃` plus one edge inside a part has dimension four, no isolated vertex, and ten edges. -/
theorem DimensionFourExtremal.drop_3.proof : DimensionFourExtremal.drop_3 := by
  intro hyp
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let a : Fin 3 ⊕ Fin 3 := Sum.inl 0
  let b : Fin 3 ⊕ Fin 3 := Sum.inl 2
  let H : SimpleGraph (Fin 3 ⊕ Fin 3) := K ⊔ edge a b
  let G : SimpleGraph (Fin 6) := H.map e
  let φ : H ≃g G := Iso.map e H
  have htransport {u w : Fin 3 ⊕ Fin 3} (hadj : H.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj
    rwa [Iso.map_apply e H u, Iso.map_apply e H w] at h
  have hpull {u w : Fin 6} (hadj : G.Adj u w) : H.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e H (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e H (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  have hne : a ≠ b := by decide
  have hnotK : ¬ K.Adj a b := by
    simp [K, completeBipartiteGraph, a, b, Sum.isLeft, Sum.isRight]
  have hdisj : Disjoint K.edgeSet (edge a b).edgeSet := by
    rw [edgeSet_edge_of_ne hne, Set.disjoint_singleton_right, mem_edgeSet]
    exact hnotK
  have hH : H.edgeSet.ncard = 10 := by
    have hunion : H.edgeSet = K.edgeSet ∪ (edge a b).edgeSet := by
      simp [H, edgeSet_sup]
    rw [hunion, Set.ncard_union_eq hdisj,
      completeBipartiteGraph_three_three_edgeSet_ncard, edgeSet_edge_of_ne hne,
      Set.ncard_singleton]
  have hG : G.edgeSet.ncard = 10 := (Set.ncard_congr' φ.mapEdgeSet).symm.trans hH
  have hdim : HasDimension G 4 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfCross, hfLeft⟩ :=
        completeBipartiteGraph_three_three_unitDistance_withLeft
      refine ⟨fun x => f (e.symm x), hfInj.comp e.symm.injective, ?_⟩
      intro u v huv
      have hHu : H.Adj (e.symm u) (e.symm v) := hpull huv
      simp only [H, sup_adj, edge_adj a b] at hHu
      rcases hHu with hK | ⟨hor, _⟩
      · exact hfCross _ _ hK
      · rcases hor with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · change dist (f (e.symm u)) (f (e.symm v)) = 1
          rw [hu, hv]
          exact hfLeft
        · change dist (f (e.symm u)) (f (e.symm v)) = 1
          rw [PseudoMetricSpace.dist_comm, hu, hv]
          exact hfLeft
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g, hgInj, hgDist⟩ := hm
      have hHrep :
          ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin m),
            Function.Injective f ∧ ∀ u v, H.Adj u v → dist (f u) (f v) = 1 :=
        ⟨fun x => g (e x), hgInj.comp e.injective,
          fun u v huv => hgDist (e u) (e v) (htransport huv)⟩
      have hKrep := unitDistance_of_le (le_sup_left : K ≤ H) hHrep
      have hmle : ¬ m ≤ 3 := fun hle =>
        not_exists_completeBipartiteGraph_three_three_unitDistance_three
          (unitDistance_of_fin_le hle hKrep)
      exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
  have hnbr : ∀ v : Fin 6, ∃ w : Fin 6, G.Adj v w := by
    intro v
    obtain ⟨w, hw⟩ : ∃ w, K.Adj (e.symm v) w := by
      cases e.symm v with
      | inl _ => exact ⟨Sum.inr 0, by simp [K, completeBipartiteGraph]⟩
      | inr _ => exact ⟨Sum.inl 0, by simp [K, completeBipartiteGraph]⟩
    exact ⟨e w, by
      simpa [e.apply_symm_apply] using htransport ((le_sup_left : K ≤ H) hw)⟩
  have hnot : ¬ Nonempty (G ≃g K) := by
    intro ⟨ψ⟩
    have hc := Set.ncard_congr' ψ.mapEdgeSet
    rw [hG, completeBipartiteGraph_three_three_edgeSet_ncard] at hc
    exact absurd hc (by decide : (10 : ℕ) ≠ 9)
  exact hnot (hyp 6 G hdim hnbr)

/-- `K₃,₃` plus an isolated vertex has dimension four and nine edges, and is not `K₃,₃`. -/
theorem DimensionFourExtremal.drop_4.proof : DimensionFourExtremal.drop_4 := by
  intro hyp
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let K6 : SimpleGraph (Fin 6) := K.map e
  let ι : Fin 6 ↪ Fin 7 := Fin.castSuccEmb
  let G : SimpleGraph (Fin 7) := K6.map ι
  let φ : K ≃g K6 := Iso.map e K
  have hpull {u w : Fin 6} (hadj : K6.Adj u w) : K.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e K (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e K (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  have hK6 : K6.edgeSet.ncard = 9 :=
    (Set.ncard_congr' φ.mapEdgeSet).symm.trans
      completeBipartiteGraph_three_three_edgeSet_ncard
  have hG : G.edgeSet.ncard = 9 := by
    have hset : G.edgeSet = ι.sym2Map '' K6.edgeSet := by
      rw [show G = K6.map ι from rfl]
      exact edgeSet_map ι K6
    rw [hset, Set.ncard_image_of_injective K6.edgeSet ι.sym2Map.injective, hK6]
  have hdim : HasDimension G 4 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfDist⟩ := completeBipartiteGraph_three_three_unitDistance
      let f6 : Fin 6 → EuclideanSpace ℝ (Fin 4) := fun x => f (e.symm x)
      have hf6Inj : Function.Injective f6 := hfInj.comp e.symm.injective
      obtain ⟨p, hp⟩ := (Set.finite_range f6).exists_notMem
      let g : Fin 7 → EuclideanSpace ℝ (Fin 4) := fun i =>
        if h : (i : ℕ) < 6 then f6 ⟨i, h⟩ else p
      have hg_lt {i : Fin 7} (h : (i : ℕ) < 6) : g i = f6 ⟨i, h⟩ := by
        have heq : g i = (if h' : (i : ℕ) < 6 then f6 ⟨i, h'⟩ else p) := rfl
        rw [dif_pos h] at heq
        exact heq
      have hg_ge {i : Fin 7} (h : ¬ (i : ℕ) < 6) : g i = p := by
        have heq : g i = (if h' : (i : ℕ) < 6 then f6 ⟨i, h'⟩ else p) := rfl
        rw [dif_neg h] at heq
        exact heq
      refine ⟨g, ?_, ?_⟩
      · intro a b hab
        by_cases ha : (a : ℕ) < 6
        · by_cases hb : (b : ℕ) < 6
          · exact Fin.ext (congrArg (fun j : Fin 6 => (j : ℕ))
              (hf6Inj ((hg_lt ha).symm.trans (hab.trans (hg_lt hb)))))
          · exact False.elim
              (hp ⟨⟨a, ha⟩, (hg_lt ha).symm.trans (hab.trans (hg_ge hb))⟩)
        · by_cases hb : (b : ℕ) < 6
          · exact False.elim
              (hp ⟨⟨b, hb⟩, (hg_lt hb).symm.trans (hab.symm.trans (hg_ge ha))⟩)
          · have ha6 : (a : ℕ) = 6 := by have := a.isLt; omega
            have hb6 : (b : ℕ) = 6 := by have := b.isLt; omega
            exact Fin.ext (ha6.trans hb6.symm)
      · intro u v huv
        obtain ⟨u', v', hu', rfl, rfl⟩ := (map_adj ι K6 u v).mp huv
        have hg_emb {i : Fin 6} : g (ι i) = f6 i := by
          have hlt : ((ι i : Fin 7) : ℕ) < 6 := by
            simp only [ι, Fin.castSuccEmb_apply, Fin.val_castSucc]
            exact i.isLt
          rw [hg_lt hlt]
          congr 1
        rw [hg_emb (i := u'), hg_emb (i := v')]
        exact hfDist (e.symm u') (e.symm v') (hpull hu')
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g0, hgInj, hgDist⟩ := hm
      have hKrep := unitDistance_of_embedding
        ((Embedding.map ι K6).comp φ.toEmbedding) ⟨g0, hgInj, hgDist⟩
      have hmle : ¬ m ≤ 3 := fun hle =>
        not_exists_completeBipartiteGraph_three_three_unitDistance_three
          (unitDistance_of_fin_le hle hKrep)
      exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
  have hnot : ¬ Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
    intro ⟨ψ⟩
    have hc := ψ.card_eq
    simp only [Fintype.card_fin, Fintype.card_sum] at hc
    omega
  exact hnot (hyp 7 G hdim hG)

end Erdos1007.Standalone.Mathlib.InlineErdos1007
