/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007.Standalone.Mathlib.InlineErdos1007Proof

/-!
# Unit-distance graphs of dimension four with nine edges

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace Erdos1007.Palomar

/-- A graph of dimension four with nine edges and no isolated vertex is `K₃,₃`. -/
theorem target :
    Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal :=
  Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.proof

end Erdos1007.Palomar
