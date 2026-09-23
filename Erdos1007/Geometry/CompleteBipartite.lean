/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# `K₃,₃` admits a unit-distance representation in `ℝ⁴`

The upper bound in the dimension computation `dim(K₃,₃) = 4` (blueprint node `lem:k33-dim`): with
`r = 1/√2`, place one part at `{(r, 0, 0, 0), (-r, 0, 0, 0), (0, r, 0, 0)}` and the other at
`{(0, 0, r, 0), (0, 0, -r, 0), (0, 0, 0, r)}`. Every one of the nine cross pairs differs in
exactly two coordinates by `±r`, so all nine cross-distances are one. The same difference puts
`(r, 0, 0, 0)` and `(0, r, 0, 0)` at distance one.

The lower bound is
`not_exists_completeBipartiteGraph_three_three_unitDistance_three`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 3, attributed there to Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

namespace Erdos1007

/-- The signed axis vector: `a` in coordinate `i` of `ℝ⁴`, zero in the other three coordinates. -/
private def svec (i : Fin 4) (a : ℝ) : EuclideanSpace ℝ (Fin 4) := PiLp.single 2 i a

/-- The placement of the six vertices: each part occupies two disjoint coordinate axes, with one
axis carrying both signs and one axis carrying only `+`. -/
private def pt (r : ℝ) : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4)
  | .inl 0 => svec (0 : Fin 4) r
  | .inl 1 => svec (0 : Fin 4) (-r)
  | .inl 2 => svec (1 : Fin 4) r
  | .inr 0 => svec (2 : Fin 4) r
  | .inr 1 => svec (2 : Fin 4) (-r)
  | .inr 2 => svec (3 : Fin 4) r

/-- The squared coordinate-distance sum for two signed axis vectors on distinct axes: only the
two occupied coordinates contribute, one `a²` and one `b²`. -/
private theorem sq_dist_svec {a b : ℝ} {i j : Fin 4} (h : i ≠ j) :
    ∑ k : Fin 4, dist ((svec i a).ofLp k) ((svec j b).ofLp k) ^ 2 = a ^ 2 + b ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [svec, PiLp.single_apply, Fin.sum_univ_four, Real.dist_eq, sq_abs] <;> ring

@[expose] public section

/-- The placement of `K₃,₃` in `ℝ⁴` realises every cross edge, and also the segment joining
`(r, 0, 0, 0)` to `(0, r, 0, 0)`, as a unit segment. -/
theorem completeBipartiteGraph_three_three_unitDistance_with_left :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      (∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1) ∧
      dist (f (Sum.inl 0)) (f (Sum.inl 2)) = 1 := by
  obtain ⟨r, hr2, hrpos⟩ : ∃ r : ℝ, r ^ 2 = 1 / 2 ∧ 0 < r :=
    ⟨1 / Real.sqrt 2, by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)], by positivity⟩
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  -- Two signed axis vectors with a nonzero entry agree only on the same axis with the same entry.
  have hvec_inj : ∀ i j : Fin 4, ∀ a b : ℝ, a ≠ 0 → svec i a = svec j b → i = j ∧ a = b := by
    intro i j a b ha h
    have h1 : a = if i = j then b else 0 := by
      have h2 : (svec i a).ofLp i = (svec j b).ofLp i := by rw [h]
      simp only [svec, PiLp.single_eq_same, PiLp.single_apply] at h2
      exact h2
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl] at h1
      exact ⟨rfl, h1⟩
    · rw [if_neg hij] at h1
      exact absurd h1 ha
  -- Two signed axis vectors on distinct axes, each of squared length `r² = 1/2`, are at distance 1.
  have hvec_dist : ∀ i j : Fin 4, i ≠ j → ∀ a b : ℝ,
      a ^ 2 = r ^ 2 → b ^ 2 = r ^ 2 → dist (svec i a) (svec j b) = 1 := by
    intro i j hij a b ha hb
    rw [EuclideanSpace.dist_eq, sq_dist_svec hij, ha, hb, hr2]
    norm_num
  refine ⟨pt r, ?_, ?_, ?_⟩
  · -- Injectivity: read off the axis and the sign from a placed point.
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · rfl
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv <;>
        exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv <;>
        exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · rfl
  · -- Every edge joins the two parts, whose points lie on disjoint axes.
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · simp [completeBipartiteGraph] at huv
    · fin_cases u <;> fin_cases v <;> simp only [pt] <;>
        exact hvec_dist _ _ (by simp) _ _ (by ring) (by ring)
    · fin_cases u <;> fin_cases v <;> simp only [pt] <;>
        exact hvec_dist _ _ (by simp) _ _ (by ring) (by ring)
    · simp [completeBipartiteGraph] at huv
  · rw [show pt r (Sum.inl 0) = svec (0 : Fin 4) r from rfl,
        show pt r (Sum.inl 2) = svec (1 : Fin 4) r from rfl]
    exact hvec_dist (0 : Fin 4) 1 (by decide) r r rfl rfl

/-- **Upper bound** for the dimension of `K₃,₃`: the complete bipartite graph on `3 + 3` vertices
admits an injective placement in `ℝ⁴` realising every edge as a unit segment (blueprint node
`lem:k33-dim`; Chaffee–Noble Lemma 3, attributed there to Erdős–Harary–Tutte).

With `r = 1/√2` the left part sits at `{(r, 0, 0, 0), (-r, 0, 0, 0), (0, r, 0, 0)}` and the right
part at `{(0, 0, r, 0), (0, 0, -r, 0), (0, 0, 0, r)}`; the squared distance of a cross pair is
`r² + r² = 1`. -/
theorem completeBipartiteGraph_three_three_unitDistance :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      ∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1 := by
  obtain ⟨f, hfInj, hfDist, _⟩ := completeBipartiteGraph_three_three_unitDistance_with_left
  exact ⟨f, hfInj, hfDist⟩

end

end Erdos1007
