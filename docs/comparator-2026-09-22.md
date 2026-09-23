# Comparator run, 2026-09-22

Comparator checks that `Solution.lean` proves exactly the statement in `Challenge.lean`, with only
the permitted axioms, and replays the proof through two independent kernels.

- **Tree:** the Lean sources, `comparator.json` and the Lake configuration of commit `2a8b97d`.
  That is the last commit to change any of them; every later commit changes documentation only.
  `comparator.json` as committed:
  - target `Erdos1007.Palomar.target`
  - permitted axioms `propext`, `Quot.sound`, `Classical.choice`
  - `enable_nanoda: true`
- **Tools:**
  - Comparator `c0c5a52`, the last commit on the Lean v4.33 toolchain, built here with
    `leanprover/lean4:v4.33.1` to match this project
  - its pinned `lean4export` `15f6055`
  - the NanoDa kernel, `ammkrn/nanoda_lib` `3a24072`, built with Rust 1.98.0
- **Sandbox:** none. The run used Comparator's `scripts/fake-landrun.sh`, because the real
  landrun sandbox is Linux-only. This checks the mathematics, not isolation. Palomar re-runs
  Comparator sandboxed, with its own pinned tools, and the `Palomar preflight` workflow runs that
  pipeline on GitHub.

## Result

```text
Building Challenge                       … Build completed successfully (2385 jobs).
Exporting … Erdos1007.Palomar.target … from Challenge
Building Solution                        … Build completed successfully (2441 jobs).
Exporting … Erdos1007.Palomar.target … from Solution
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

32 s wall clock and 2.8 GB peak resident memory, on a Mac mini.

The only warning in the `Challenge` build is Palomar's advertised hole: `Challenge.lean:150`,
`declaration uses 'sorry'`.

An earlier run, on commit `7d70413` before the hypothesis-drop companions and the review fixes, gave
the same result.

## Command

```sh
COMPARATOR_LANDRUN=~/src/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=~/src/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=~/src/nanoda_lib/target/release/nanoda_bin \
  lake env ~/src/comparator/.lake/build/bin/comparator comparator.json
```
