/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007.Standalone.Mathlib.InlineErdos1007

/-!
# Proofs for `InlineErdos1007`

The proof sibling. Unlike its statement module this may import the development, and it is the one
explicit exception to the standalone isolation rule.

**This module does not compile yet, and that is the honest state of the project.**
`warningAsError = true` makes each `sorry` below a hard error, so `lake build` fails until Stage 3
discharges them. Nothing here may be reported as proved while that is so. The statement module and
`Challenge.lean` do compile; they are what Stage 1 froze.

Work in progress belongs in `tmp/`; a proof moves here only once it typechecks clean.
-/

public section

namespace Erdos1007.Standalone.Mathlib.InlineErdos1007

/-- `K₂` plus an isolated vertex, placed in `ℝ¹`, has a non-edge at distance one. -/
theorem UnitDistanceEmbeddable.separating.proof : UnitDistanceEmbeddable.separating := by
  sorry

/-- A graph representable in `ℝ⁴` need not have dimension four. -/
theorem HasDimension.separating.proof : HasDimension.separating := by
  sorry

/-- `K₃,₃` has dimension four, nine edges, and no isolated vertex, so the extremal claim is not
vacuous. Half of the source paper's content. -/
theorem DimensionFourExtremal.witness.proof : DimensionFourExtremal.witness := by
  sorry

/-- **The target.** Chaffee–Noble, Australas. J. Combin. 64(2) (2016), Theorem 7. -/
theorem DimensionFourExtremal.proof : DimensionFourExtremal := by
  sorry

end Erdos1007.Standalone.Mathlib.InlineErdos1007
