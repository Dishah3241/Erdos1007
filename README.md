# Unit-distance graphs of dimension four with nine edges

A Lean 4 proof of the extremal half of Erdős problem 1007: a graph of dimension four with nine edges
and no isolated vertex is `K₃,₃`.

> A graph has **dimension** `n` when `n` is the least number such that its vertices can be placed
> injectively in `ℝⁿ` with every edge a unit segment (Erdős, Harary and Tutte, 1965). House proved
> that a graph of dimension four has at least nine edges, and that nine is attained only by
> `K₃,₃`.

| | |
|---|---|
| Proof | complete: no `sorry`; only `propext`, `Classical.choice` and `Quot.sound` |
| Comparator | accepted by Lean's kernel and by NanoDa ([record](docs/comparator-2026-09-22.md)) |
| Blueprint | [web](https://dishah3241.github.io/Erdos1007/) and [PDF](https://dishah3241.github.io/Erdos1007/blueprint.pdf), built by CI from `blueprint/src/content.tex` |
| `formal-conjectures` link | [pull request #6511](https://github.com/google-deepmind/formal-conjectures/pull/6511), under review |
| Palomar entry | [PALOMAR-2026-09-23-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-23-000003&version=1), registered at commit `43f8941` ([record](docs/palomar-2026-09-22.md)) |
| Mathlib contributions | three candidates, to be generalized in a shared graph-dimension library first: equal spheres about three distinct points of `ℝ³` share at most two points; the isometry extending `EuclideanSpace` by zero; the components of a finite two-regular graph are cycles |

## Context

Erdős asked for the least number of edges of a graph of dimension four; he posed the question to
Soifer in 1992. It belongs to a line of work on `f(d)`, the least number of edges of a graph with no
unit-distance representation in `ℝᵈ`. Since `K_{d+2}` has none, `f(d) ≤ C(d + 2, 2)`, and Frankl,
Kupavskii and Swanepoel proved equality for every `d ≥ 4`, confirming a question of Erdős and
Simonovits. Dimension three is the exception: `f(3) = 9 < C(5, 2)`, because `K₃,₃` has no
representation in `ℝ³`. House's theorem makes `K₃,₃` the only such graph with nine edges, and that
uniqueness is what this repository proves. The question belongs to discrete geometry and extremal
graph theory, and specifically to the study of unit-distance representations and the dimension of
graphs.

## The statement

The theorem is `erdos_1007.variants.dimension_four_extremal` from
[google-deepmind/formal-conjectures][fc]. `Erdos1007/Standalone/Mathlib/InlineErdos1007.lean`
restates it with its two definitions inlined, so that it depends on Mathlib alone:

```lean
def DimensionFourExtremal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasDimension G 4 → G.edgeSet.ncard = 9 → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
      Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
```

`DimensionFourExtremal.proof` in `InlineErdos1007Proof.lean` proves it. `Solution.lean` restates it
as `Erdos1007.Palomar.target`, which Comparator checks against `Challenge.lean`.

Why the statement means the claim:

- **It is upstream's statement.** With both builds loaded together, it equals the type of
  upstream's declaration by `rfl`, and the proof elaborates against that type
  ([record](docs/upstream-check-2026-09-22.md)).
- **Every hypothesis is needed.** `DimensionFourExtremal.drop2`, `drop3` and `drop4` are
  kernel-checked counterexamples to the statement with each hypothesis removed. The no-isolated-vertex
  hypothesis matters because `K₃,₃` plus an isolated vertex has the same dimension and edge count.
- **The hypotheses can all hold.** `DimensionFourExtremal.witness.proof` shows that `K₃,₃` has
  dimension exactly four, so the theorem is not vacuous.
- **Each definition means what it says.** [`docs/compass.md`](docs/compass.md) lists what every
  statement-level declaration must mean, and each definition has a separating example.

## The proof

It follows Chaffee and Noble's proof, Theorem 7 of the paper below.

1. Every graph with at most eight edges has a unit-distance representation in `ℝ³` (their Theorem
   6), by induction on vertices plus edges. Delete a vertex of degree at most two. If it had two
   neighbours, join them by an edge; the graph still has at most eight edges. Place the smaller
   graph. The two neighbours are now at distance one, so the unit spheres about them meet in a
   circle, and the vertex goes back on that circle, away from the finitely many points already
   used. If instead every degree is at least three, the graph is `K₄` or a subgraph of `K₅ − e`,
   and both have a representation in `ℝ³`.
2. Now take a nine-edge graph of dimension four with no isolated vertex. A vertex of degree one or
   two would give, by the same deletion, a representation in `ℝ³`, contradicting dimension four.
   So every degree is at least three.
3. Then `18 = 2|E| ≥ 3|V|` gives at most six vertices, and `K₄` has only six edges, so there are
   five or six.
4. On five vertices, nine edges leave exactly one non-edge, so the graph is `K₅ − e`: a
   contradiction.
5. On six vertices the graph is three-regular, so its complement is two-regular: `C₆` or two
   triangles. The complement of `C₆` is the triangular prism, which has a representation in the
   plane: a contradiction. Two triangles give `K₃,₃`.

Chaffee and Noble state steps 3 and 4 without argument; both are proved here.

Each step is a named Lean theorem. In `InlineErdos1007Proof.lean`, namespace
`Erdos1007.Standalone.Mathlib.InlineErdos1007`:

| Step | Declaration |
|---|---|
| 2 | `degree_ge_three_of_hasDimension_four_nine_edges` |
| 4 | `not_hasDimension_four_nine_edges_fin_five` |
| 5 | `iso_completeBipartiteGraph_three_three_of_hasDimension_four_fin_six` |
| `K₃,₃` has dimension four | `hasDimension_completeBipartiteGraph_three_three` |
| the theorem | `DimensionFourExtremal.proof`, which combines them |

In the namespace `Erdos1007`:

| Step | Declaration |
|---|---|
| 1 | `unitDistance_of_edgeFinset_card_le_eight`, re-attaching by `unitDistance_extend_degree_le_two` |
| 2 | `unitDistance_of_nine_edges_degree_le_two` |
| 3 | `nine_edges_card_ge_five` and `nine_edges_minDegree_three_card_le_six` |
| 4 | `nine_edges_iso_deleteEdge`, and `completeGraph_five_deleteEdge_unitDistance` for `K₅ − e` |
| 5 | `nine_edges_six_minDegree_three`, `isRegularOfDegree_two_fin_six` and `compl_cycleGraph_six_unitDistance` |

The [blueprint](https://dishah3241.github.io/Erdos1007/) lays out the same steps as a dependency
graph.

## Checking it

With Lean `v4.33.1` and Mathlib `0df444a`, the same pins as `formal-conjectures`:

```sh
lake exe cache get
lake build
lake exe axioms && lake exe fidelity && lake exe proof-links && lake exe palomar-compatibility
lake exe module-system && lake exe standalone-mathlib && lake exe layering
lake exe style && lake exe documentation
scripts/lint-env.sh && scripts/check-palomar-challenge.sh . && scripts/audit-probes.sh
```

`scripts/audit-probes.sh` checks that each audit rejects the defect it exists to catch. The
Comparator command is in [`docs/comparator-2026-09-22.md`](docs/comparator-2026-09-22.md).

## Sources

- Joe Chaffee and Matt Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*,
  [Australas. J. Combin. **64(2)** (2016), 327–333][cn], Theorems 6 and 7. The proof of record; it
  is open access.
- Roger F. House, *A 4-dimensional graph has at least 9 edges*, Discrete Math. **313(18)** (2013),
  1783–1789, [doi:10.1016/j.disc.2013.05.005](https://doi.org/10.1016/j.disc.2013.05.005). The
  first proof. It was not consulted.
- Paul Erdős, Frank Harary and William T. Tutte, *On the dimension of a graph*, Mathematika **12**
  (1965), 118–122, [doi:10.1112/S0025579300005222](https://doi.org/10.1112/S0025579300005222).
- Nóra Frankl, Andrey Kupavskii and Konrad J. Swanepoel, *Embedding graphs in Euclidean space*,
  J. Combin. Theory Ser. A **171** (2020), 105146,
  [doi:10.1016/j.jcta.2019.105146](https://doi.org/10.1016/j.jcta.2019.105146). Context: `f(d)` for
  every `d ≥ 4`.
- T. F. Bloom, Erdős Problem #1007, <https://www.erdosproblems.com/1007>.

## Prior formalization

Boris Alexeev's [`plby/lean-proofs`][plby] proves the other half of the problem,
`formal-conjectures`' `erdos_1007`: the least number of edges of a graph of dimension four is nine.
He made it with Aristotle. It does not prove the uniqueness statement proved here. That repository
has no licence, and nothing from it is used here.

## How this was made

AI agents wrote the Lean under the direction of its owner, who signed off on what the statement
means and approved publication. [`formalization.yaml`](formalization.yaml) names
every model and harness, phase by phase:

- **Statement:** Claude Opus 5.
- **Adversarial statement review:** gpt-6-astra, through Codex.
- **Proof:** Grok 4.7 workers, with two leaves proved by GLM-5.3-flash through pi.
- **Independent proof review:** Claude Opus 5.5.

No human has reviewed the proof itself. Its correctness rests on the kernel checks above.

## Licence

Apache-2.0. See [`LICENSE`](LICENSE).

[fc]: https://github.com/google-deepmind/formal-conjectures
[cn]: https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p327.pdf
[plby]: https://github.com/plby/lean-proofs
