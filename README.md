# Unit-distance graphs of dimension four with nine edges

A Lean certification of the extremal half of Erdős problem 1007.

> A graph has **dimension** `n` when `n` is least such that its vertices can be placed injectively
> in `ℝⁿ` with every edge realised as a unit segment. The least number of edges in a graph of
> dimension four is nine, and nine is attained **only** by `K₃,₃`.

This repository targets the "only by `K₃,₃`" half.

| | |
|---|---|
| Stage | **2 — blueprint written**; Compass sign-off pending ([`docs/compass.md`](docs/compass.md)) |
| Builds | **No, by design.** See below. |
| Palomar entry | not submitted |
| `formal_proof` PR | not opened |
| Mathlib PR | not opened |
| Writeup | not published |

## What is and is not true right now

`Erdos1007/Standalone/Mathlib/InlineErdos1007.lean` and `Challenge.lean` compile. They carry the
statement and nothing else.

`InlineErdos1007Proof.lean` and `Solution.lean` do **not** compile: every proof is `sorry`, and
`warningAsError = true` makes that a hard error. `lake build` fails. **Nothing in this repository
is proved.** That is the accurate state of a project before Stage 3 finishes, and it is not a
defect to be worked around — see `../../docs/PLAYBOOK.md`.

## Source

The statement reproduces `erdos_1007.variants.dimension_four_extremal` from
[google-deepmind/formal-conjectures][fc] with its definitions inlined so the file rests on Mathlib
alone. That upstream statement carries the Formal Conjectures project's own review, which is why
this target was chosen: the least mechanically checkable step was already performed by someone
else.

Proof of record: Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*,
[Australas. J. Combin. **64(2)** (2016), 327–333][cn], Theorem 7 — diamond open access, so anyone
can check this work against it. The original is House, *A 4-dimensional graph has at least 9
edges*, Discrete Math. **313(18)** (2013), 1783–1789, which is paywalled and was not consulted.

[fc]: https://github.com/google-deepmind/formal-conjectures
[cn]: https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p327.pdf

## Proof spine

1. Every graph with at most eight edges is representable in `ℝ³` — delete a vertex of degree at
   most two and re-place it on the circle where two unit spheres meet; at eight edges with minimum
   degree at least three the degree sequence `(4,3,3,3,3)` makes it a subgraph of `K₅ − e`.
2. So a nine-edge graph of dimension four has minimum degree at least three.
3. `18 = 2|E| ≥ 3|V|` forces `|V| ∈ {5, 6}`.
4. `|V| = 6` is three-regular; its complement is `C₆` (the prism, which embeds in `ℝ²`, a
   contradiction) or `K₃ ⊔ K₃`, giving `K₃,₃`.

Chaffee–Noble import four results (their Lemmas 1–4) from Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122; three of them are needed here. The
blueprint in `blueprint/src/content.tex` has the full dependency graph.

## Prior formalization

[`plby/lean-proofs`][plby] proves `IsLeast {...} 9` — that the minimum **is** nine — and does not
prove the uniqueness variant targeted here. Its machinery overlaps; its target does not. That
repository carries **no licence**, so nothing in it may be copied here, and this development is
independent.

[plby]: https://github.com/plby/lean-proofs

## Gates

```sh
lake build && lake exe axioms && lake exe fidelity && lake exe module-system \
  && lake exe standalone-mathlib && lake exe proof-links && lake exe style \
  && lake exe documentation && lake exe layering && lake exe palomar-compatibility \
  && leanblueprint checkdecls && scripts/audit-probes.sh
```

Currently `scripts/check-palomar-challenge.sh .` passes: `Challenge.lean` is generated from the
statement source, so it cannot drift from it.
