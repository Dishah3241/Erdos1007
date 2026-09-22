/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `K₅ − e` in `ℝ³`

The upper bound for `dim(K₅ − e) = 3`. Delete the edge between vertices `3` and `4` from the
complete graph on `Fin 5` by `SimpleGraph.deleteEdges`, written
`(⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)}`. Place `{0, 1, 2}` as the unit equilateral
triangle `(0, 0, 0)`, `(1, 0, 0)`, `(1/2, √3/2, 0)`, and place `3` and `4` at the apexes
`(1/2, √3/6, ±√(2/3))` of the two regular tetrahedra on that triangle. Every remaining edge has
length one. The apexes themselves are at distance `2√(2/3)`, which is not one; that pair is the
deleted edge.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 2, attributed there to Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122. Blueprint node `lem:kn-minus-e`.
The placement is a witness that `dim(K₅ − e) ≤ 3`.
-/

namespace Erdos1007

noncomputable section

private def xCoord : Fin 5 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1 / 2
  | 3 => 1 / 2
  | 4 => 1 / 2

private def yCoord : Fin 5 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => Real.sqrt 3 / 2
  | 3 => Real.sqrt 3 / 6
  | 4 => Real.sqrt 3 / 6

private def zCoord : Fin 5 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => Real.sqrt (2 / 3)
  | 4 => -Real.sqrt (2 / 3)

private def pt (i : Fin 5) : EuclideanSpace ℝ (Fin 3) := !₂[xCoord i, yCoord i, zCoord i]

private lemma dist_sq (u v : Fin 5) :
    dist (pt u) (pt v) ^ 2 =
      (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 + (zCoord u - zCoord v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt, Real.dist_eq, sq_abs]

private lemma dist_of_sq {u v : Fin 5}
    (h : (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 +
      (zCoord u - zCoord v) ^ 2 = 1) :
    dist (pt u) (pt v) = 1 := by
  have hsq : dist (pt u) (pt v) ^ 2 = 1 := by rw [dist_sq, h]
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 5) :
    (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 + (zCoord u - zCoord v) ^ 2 =
      (xCoord v - xCoord u) ^ 2 + (yCoord v - yCoord u) ^ 2 + (zCoord v - zCoord u) ^ 2 := by
  ring

private lemma equil : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma apexFromCorner :
    (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 6) ^ 2 + (Real.sqrt (2 / 3)) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  norm_num

private lemma apexFromTop :
    (Real.sqrt 3 / 2 - Real.sqrt 3 / 6) ^ 2 + (Real.sqrt (2 / 3)) ^ 2 = 1 := by
  have h : Real.sqrt 3 / 2 - Real.sqrt 3 / 6 = Real.sqrt 3 / 3 := by ring
  rw [h, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  norm_num

private lemma sq_01 :
    (xCoord 0 - xCoord 1) ^ 2 + (yCoord 0 - yCoord 1) ^ 2 + (zCoord 0 - zCoord 1) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]; norm_num

private lemma sq_02 :
    (xCoord 0 - xCoord 2) ^ 2 + (yCoord 0 - yCoord 2) ^ 2 + (zCoord 0 - zCoord 2) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert equil using 1
  ring

private lemma sq_12 :
    (xCoord 1 - xCoord 2) ^ 2 + (yCoord 1 - yCoord 2) ^ 2 + (zCoord 1 - zCoord 2) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert equil using 1
  ring

private lemma sq_03 :
    (xCoord 0 - xCoord 3) ^ 2 + (yCoord 0 - yCoord 3) ^ 2 + (zCoord 0 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromCorner using 1
  ring

private lemma sq_13 :
    (xCoord 1 - xCoord 3) ^ 2 + (yCoord 1 - yCoord 3) ^ 2 + (zCoord 1 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromCorner using 1
  ring

private lemma sq_23 :
    (xCoord 2 - xCoord 3) ^ 2 + (yCoord 2 - yCoord 3) ^ 2 + (zCoord 2 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromTop using 1
  ring

private lemma sq_04 :
    (xCoord 0 - xCoord 4) ^ 2 + (yCoord 0 - yCoord 4) ^ 2 + (zCoord 0 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromCorner using 1
  ring

private lemma sq_14 :
    (xCoord 1 - xCoord 4) ^ 2 + (yCoord 1 - yCoord 4) ^ 2 + (zCoord 1 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromCorner using 1
  ring

private lemma sq_24 :
    (xCoord 2 - xCoord 4) ^ 2 + (yCoord 2 - yCoord 4) ^ 2 + (zCoord 2 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert apexFromTop using 1
  ring

private lemma sqrt23_ne_zero : Real.sqrt (2 / 3) ≠ 0 :=
  ne_of_gt (by positivity)

private lemma neg_sqrt23_ne_zero : -Real.sqrt (2 / 3) ≠ 0 := by
  intro h
  exact sqrt23_ne_zero (neg_eq_zero.mp h)

private lemma sqrt23_ne_neg : Real.sqrt (2 / 3) ≠ -Real.sqrt (2 / 3) := by
  intro h
  have hpos : (0 : ℝ) < Real.sqrt (2 / 3) := by positivity
  nlinarith

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : xCoord u = xCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hz : zCoord u = zCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v <;> simp only [xCoord, zCoord] at hx hz
  · rfl
  · exact absurd hx (by norm_num)
  · exact absurd hx (by norm_num)
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hx (by norm_num)
  · rfl
  · exact absurd hx (by norm_num)
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hx (by norm_num)
  · exact absurd hx (by norm_num)
  · rfl
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · rfl
  · exact absurd hz sqrt23_ne_neg
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz.symm sqrt23_ne_neg
  · rfl

@[expose] public section

/-- **Upper bound** for the dimension of `K₅ − e`: the complete graph on five vertices with the
edge `s(3, 4)` deleted admits a unit-distance representation in `ℝ³` (blueprint node
`lem:kn-minus-e`).

Vertices `0`, `1` and `2` form a unit equilateral triangle, and `3` and `4` are the two apexes of
the regular tetrahedra on that triangle. Chaffee–Noble Lemma 2, attributed there to
Erdős–Harary–Tutte. -/
theorem completeGraph_five_deleteEdge_unitDistance :
    ∃ f : Fin 5 → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)}).Adj u v →
        dist (f u) (f v) = 1 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order. The deleted edge is `(3, 4)`.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_01
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact dist_of_sq ((sq_comm 0 1).symm.trans sq_01)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_12
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact dist_of_sq ((sq_comm 1 2).symm.trans sq_12)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_23
  · exact dist_of_sq sq_24
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact dist_of_sq ((sq_comm 2 3).symm.trans sq_23)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)

end

end

end Erdos1007
