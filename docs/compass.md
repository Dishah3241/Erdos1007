# Compass list

The declarations whose meaning decides whether the target theorem says what it claims. This is the
owner's whole review surface under `../../docs/PLAYBOOK.md` stage 1, step 5. Everything else,
including the whole proof interior, is checked by the kernel and the gates.

All six project declarations are in `Erdos1007/Standalone/Mathlib/InlineErdos1007.lean`, namespace
`Erdos1007.Standalone.Mathlib.InlineErdos1007`.

**Owner sign-off: provisional, 2026-09-21.** The owner agreed "for now". This unblocks Stage 3.
The owner must confirm it again before anything lands (Stage 5), and any change to a row above
cancels the sign-off.

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `UnitDistanceEmbeddable G n` | an injective placement of the vertices in `ℝⁿ` with every edge at distance one | Non-edges are unconstrained. That is the source's reading, not the stricter unit-distance *graph*. |
| 2 | `HasDimension G n` | `n` is the **least** such dimension | `IsLeast`, not mere membership. Membership would make the target false. |
| 3 | `DimensionFourExtremal` | dimension four, nine edges and no isolated vertex imply `G ≃g K₃,₃` | Vertices are `Fin n`, so the graph is finite. The no-isolated-vertex hypothesis is necessary: adding an isolated vertex to `K₃,₃` breaks the conclusion. |
| 4 | `DimensionFourExtremal.witness` | some graph meets all three hypotheses at once | Guards against vacuity. `K₃,₃` is the intended witness, and proving it needs `dim K₃,₃ = 4`. |
| 5 | `UnitDistanceEmbeddable.separating` | some valid placement puts a **non-edge** at distance one | It asks for one looser placement, not for the absence of any strict placement. Red-team finding 1. |
| 6 | `HasDimension.separating` | some graph **with an edge** is representable in `ℝ⁴` without having dimension four | Requiring an edge rules out the empty-graph degenerate case. Red-team finding 3. |
| 7 | Mathlib `completeBipartiteGraph (Fin 3) (Fin 3)` | `K₃,₃` on `Fin 3 ⊕ Fin 3` | This is a root-namespace declaration, not `SimpleGraph.completeBipartiteGraph`. |
| 8 | Mathlib `G.edgeSet.ncard = 9` | exactly nine edges | `ncard` is `0` on an infinite set, but `Fin n` is finite, so this is the true count. |

Inherited provenance: rows 1–3 reproduce `erdos_1007.variants.dimension_four_extremal` from
`formal-conjectures`. The adversarial review checked that they agree with it by `rfl`
(`red-team-2026-09-20.md`). Rows 4–6 are this project's own and have no upstream review.
