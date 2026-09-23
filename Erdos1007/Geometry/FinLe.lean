/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Function.Basic

/-!
# Unit-distance representations raise the ambient dimension

A unit-distance representation of a graph in `ℝⁿ` is an injective placement of its vertices in
which every edge is a segment of length one. For `n ≤ m`, appending zero coordinates carries that
placement into `ℝᵐ`. Distances are unchanged because the new coordinates agree, and the placement
stays injective because the original coordinates still separate vertices.

## References

Erdős, Harary and Tutte, *On the dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

namespace Erdos1007

noncomputable section

/-- The vector in `ℝᵐ` obtained by appending zero coordinates to a vector of `ℝⁿ`. -/
private def appendZero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2
    (Function.extend (Fin.castLE h) (fun i => x i) (fun _ => (0 : ℝ)))

/-- A coordinate in the image of `Fin.castLE` is copied from the original vector. -/
private lemma appendZero_castLE {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : appendZero h x (Fin.castLE h i) = x i := by
  simp only [appendZero]
  exact (Fin.castLE_injective h).extend_apply (fun i => x i) (fun _ => (0 : ℝ)) i

/-- A coordinate outside the image of `Fin.castLE` is an appended zero. -/
private lemma appendZero_eq_zero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    {j : Fin m} (hj : j ∉ Set.range (Fin.castLE h)) : appendZero h x j = 0 := by
  simp only [appendZero]
  exact Function.extend_apply' (fun i => x i) (fun _ => (0 : ℝ)) j hj

/-- Appending the same zero coordinates preserves Euclidean distance. -/
private lemma dist_appendZero {n m : ℕ} (h : n ≤ m) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (appendZero h x) (appendZero h y) = dist x y := by
  have hsum :
      (∑ j : Fin m, dist (appendZero h x j) (appendZero h y j) ^ 2) =
        ∑ i : Fin n, dist (x i) (y i) ^ 2 := by
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
        (fun i => dist (x i) (y i) ^ 2)
        (fun j => dist (appendZero h x j) (appendZero h y j) ^ 2) ?_ ?_).symm
    · intro j hj
      rw [appendZero_eq_zero h x hj, appendZero_eq_zero h y hj, dist_self,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · intro i
      rw [appendZero_castLE, appendZero_castLE]
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, hsum]

/-- Appending zero coordinates is an injective map of Euclidean spaces. -/
private lemma appendZero_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (appendZero h) := by
  intro x y hxy
  ext i
  simpa [appendZero_castLE] using
    congr_arg (fun z : EuclideanSpace ℝ (Fin m) => z (Fin.castLE h i)) hxy

@[expose] public section

/-- A unit-distance representation of `G` in `ℝⁿ` yields one in `ℝᵐ` whenever `n ≤ m`.

The placement in `ℝᵐ` appends zero coordinates to the placement in `ℝⁿ`. Injectivity and edge
lengths are preserved because the extra coordinates agree. -/
theorem unitDistance_of_fin_le {V : Type*} {G : SimpleGraph V} {n m : ℕ} (h : n ≤ m) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin m), Function.Injective g ∧
        ∀ u v, G.Adj u v → dist (g u) (g v) = 1 := by
  rintro ⟨f, hfInj, hfDist⟩
  refine ⟨appendZero h ∘ f, (appendZero_injective h).comp hfInj, ?_⟩
  intro u v huv
  rw [Function.comp_apply, Function.comp_apply, dist_appendZero h, hfDist u v huv]

end

end

end Erdos1007
