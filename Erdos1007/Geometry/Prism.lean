/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The triangular prism in the plane

The complement of the hexagon `C₆` is the triangular prism. In `(cycleGraph 6)ᶜ` the vertex `i`
is adjacent to `i + 2`, `i + 3` and `i + 4`, so the edges are the triangles `{0, 2, 4}` and
`{1, 3, 5}` together with the matching `0–3`, `2–5`, `4–1`.

Place the first triangle as a unit equilateral triangle and the second as its translate by
`(0, 1)`:
`0 ↦ (0, 0)`, `2 ↦ (1, 0)`, `4 ↦ (1/2, √3/2)`,
`3 ↦ (0, 1)`, `5 ↦ (1, 1)`, `1 ↦ (1/2, 1 + √3/2)`.
Each of the nine edges is then a unit segment, so the prism admits a unit-distance representation
in `ℝ²`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333. The six points above are their placement
`(0,0), (1,0), (0,1), (1,1), (1/2, √3/2), (1/2, 1 + √3/2)`, relabelled in the order
`A, B, C, D, E, F ↦ 0, 2, 3, 5, 4, 1` so that the triangles are the even and odd vertices of `C₆`.
Blueprint node `lem:prism-planar`.
-/

namespace Erdos1007

noncomputable section

private def xCoord : Fin 6 → ℝ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 0
  | 4 => 1 / 2
  | 5 => 1

private def yCoord : Fin 6 → ℝ
  | 0 => 0
  | 1 => 1 + Real.sqrt 3 / 2
  | 2 => 0
  | 3 => 1
  | 4 => Real.sqrt 3 / 2
  | 5 => 1

private def pt (i : Fin 6) : EuclideanSpace ℝ (Fin 2) := !₂[xCoord i, yCoord i]

private lemma dist_sq (u v : Fin 6) :
    dist (pt u) (pt v) ^ 2 = (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [pt, Real.dist_eq, sq_abs]

private lemma dist_of_sq {u v : Fin 6}
    (h : (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 = 1) :
    dist (pt u) (pt v) = 1 := by
  have hsq : dist (pt u) (pt v) ^ 2 = 1 := by rw [dist_sq, h]
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 6) :
    (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 =
      (xCoord v - xCoord u) ^ 2 + (yCoord v - yCoord u) ^ 2 := by
  ring

private lemma equil : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sq_02 : (xCoord 0 - xCoord 2) ^ 2 + (yCoord 0 - yCoord 2) ^ 2 = 1 := by
  simp only [xCoord, yCoord]; norm_num

private lemma sq_03 : (xCoord 0 - xCoord 3) ^ 2 + (yCoord 0 - yCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord]; norm_num

private lemma sq_04 : (xCoord 0 - xCoord 4) ^ 2 + (yCoord 0 - yCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord]
  convert equil using 1
  ring

private lemma sq_13 : (xCoord 1 - xCoord 3) ^ 2 + (yCoord 1 - yCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord]
  convert equil using 1
  ring

private lemma sq_14 : (xCoord 1 - xCoord 4) ^ 2 + (yCoord 1 - yCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord]
  ring

private lemma sq_15 : (xCoord 1 - xCoord 5) ^ 2 + (yCoord 1 - yCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord]
  convert equil using 1
  ring

private lemma sq_24 : (xCoord 2 - xCoord 4) ^ 2 + (yCoord 2 - yCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord]
  convert equil using 1
  ring

private lemma sq_25 : (xCoord 2 - xCoord 5) ^ 2 + (yCoord 2 - yCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord]; norm_num

private lemma sq_35 : (xCoord 3 - xCoord 5) ^ 2 + (yCoord 3 - yCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord]; norm_num

/-- Equal indices agree, and every other pair of placed points differs by a rational in some
coordinate, so the placement is injective. -/
private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : xCoord u = xCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) h
  have hy : yCoord u = yCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) h
  fin_cases u <;> fin_cases v <;> simp_all [xCoord, yCoord]

@[expose] public section

/-- The complement of the hexagon admits a unit-distance representation in the plane
(blueprint node `lem:prism-planar`).

The triangles `{0, 2, 4}` and `{1, 3, 5}` are unit equilateral triangles a distance one apart,
and the matching between them is vertical. Chaffee–Noble record this placement in the proof of
their Theorem 7. -/
theorem compl_cycleGraph_six_unitDistance :
    ∃ f : Fin 6 → EuclideanSpace ℝ (Fin 2), Function.Injective f ∧
      ∀ u v, (SimpleGraph.cycleGraph 6)ᶜ.Adj u v → dist (f u) (f v) = 1 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq sq_15
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_24
  · exact dist_of_sq sq_25
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_35
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact dist_of_sq ((sq_comm 2 5).symm.trans sq_25)
  · exact dist_of_sq ((sq_comm 3 5).symm.trans sq_35)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)

end

end

end Erdos1007
