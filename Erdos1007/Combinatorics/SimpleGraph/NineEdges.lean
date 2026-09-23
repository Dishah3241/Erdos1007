/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Nine edges forces five, six, or nothing larger

A simple graph with nine edges has at least five vertices. The complete graph on four vertices
has `Nat.choose 4 2 = 6` edges, and every simple graph on `n` vertices has at most `n.choose 2`
edges, so four or fewer vertices cannot carry nine edges.

If in addition every degree is at least three, the handshaking lemma gives
`∑ v, degree v = 2 * 9 = 18 ≥ 3 * Fintype.card V`, so the graph has at most six vertices.

## References

Blueprint node `lem:at-least-five`. Blueprint node `lem:at-most-six`. Chaffee and Noble,
*Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J. Combin. **64(2)**
(2016), 327–333, pass from a nine-edge graph to the five-vertex and six-vertex cases without
recording this degree-sum comparison.
-/

namespace Erdos1007

open SimpleGraph

/-- A simple graph on at most four vertices has at most six edges. -/
private lemma edgeFinset_card_le_six_of_card_le_four
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V ≤ 4) : G.edgeFinset.card ≤ 6 := by
  calc
    G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Nat.choose 4 2 := Nat.choose_le_choose 2 hV
    _ = 6 := by decide

/-- Nine edges give degree sum eighteen. -/
private lemma sum_degrees_eq_eighteen
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) : ∑ v, G.degree v = 18 := by
  rw [G.sum_degrees_eq_twice_card_edges, hE]

/-- Minimum degree three bounds the degree sum by three times the number of vertices. -/
private lemma three_mul_card_le_sum_degrees
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, 3 ≤ G.degree v) : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
  calc
    3 * Fintype.card V = ∑ _v : V, 3 := by
      rw [Nat.mul_comm, ← Finset.card_univ, ← Finset.sum_const_nat fun _ _ => rfl]
    _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v

@[expose] public section

-- `[DecidableEq V]` belongs to the fixed statement. The inequalities do not apply it:
-- `card_edgeFinset_le_card_choose_two` obtains vertex equality from `classical`.
set_option linter.unusedDecidableInType false

/-- **At least five vertices.** A simple graph with nine edges has at least five vertices.

`K₄` has six edges, and `Nat.choose 4 2 = 6`, so a simple graph on at most four vertices has at
most six edges. Blueprint node `lem:at-least-five`. -/
theorem nine_edges_card_ge_five
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card = 9) : 5 ≤ Fintype.card V := by
  by_contra hlt
  have hV : Fintype.card V ≤ 4 := by omega
  have hle : G.edgeFinset.card ≤ 6 := edgeFinset_card_le_six_of_card_le_four hV
  omega

/-- **At most six vertices.** A simple graph with nine edges and minimum degree at least three
has at most six vertices.

The handshaking lemma gives `∑ v, G.degree v = 2 * 9 = 18`, and the degree hypothesis gives
`3 * Fintype.card V ≤ ∑ v, G.degree v`. Blueprint node `lem:at-most-six`. Chaffee and Noble
pass to the five-vertex and six-vertex cases without recording this comparison. -/
theorem nine_edges_minDegree_three_card_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Fintype.card V ≤ 6 := by
  have hsum : ∑ v, G.degree v = 18 := sum_degrees_eq_eighteen hE
  have hlow : 3 * Fintype.card V ≤ ∑ v, G.degree v := three_mul_card_le_sum_degrees hdeg
  omega

end

end Erdos1007
