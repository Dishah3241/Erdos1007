/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Structure and environment-walking helpers follow `scripts/ProofLinks.lean` from
gaearon/conway-refinement, Apache-2.0:
https://github.com/gaearon/conway-refinement/blob/main/scripts/ProofLinks.lean
-/
module

import Lean

/-!
# Audit statement fidelity

`lake build` rejects `sorry`. `lake exe axioms` rejects every axiom outside the permitted three.
Neither notices that a theorem is *vacuously true*, that a hypothesis is *decorative*, or that a
definition does not mean what its name says. Those are the defects an expert review still finds in
a mechanically clean AI formalization (arXiv 2606.13925), and they are exactly the defects a
reviewer who reads Lean but not mathematical prose cannot catch by reading.

This audit makes the authoring obligations for those defects mechanical. For every closed
proposition `C` in a reader-facing statement module it requires:

* `C.witness` — evidence that `C`'s hypotheses can be jointly satisfied. A theorem whose
  hypotheses are unsatisfiable is true and proves nothing.

and for every definition `D` in such a module:

* `D.separating` — a nondegenerate example distinguishing `D` from the nearest plausible wrong
  definition. Compilation does not establish that `IsRegular` means regular.

A companion declaration must mention the declaration it is about, and must not be `True`. That
catches the obvious way to satisfy this audit without doing the work:
`theorem C.witness : True := trivial`.

What this audit does *not* do: derive the witness itself, or run the hypothesis-drop test. Those
stay human-directed, per `docs/PLAYBOOK.md` stage 1. This checks that the obligations exist, are
about the right thing, and are not vacuous.

Run after `lake build`.
-/

open Lean

private def isolatedDirs : Array System.FilePath := #[
  "Erdos1007/Standalone/Mathlib",
]

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private partial def collectLeanFiles
    (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      if !entry.path.components.contains "Support" then
        files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

/-- Statement modules only. A `FooProof` sibling carries proofs, not claims. -/
private def isStatementFile (path : System.FilePath) : Bool :=
  !path.toString.endsWith "Proof.lean"

private def statementModules : IO (Array Name) := do
  let mut modules := #[]
  for directory in isolatedDirs do
    for file in ← collectLeanFiles directory do
      if isStatementFile file then
        modules := modules.push (pathToModule file)
  return modules

private def declarationType : ConstantInfo → Expr
  | .axiomInfo v | .defnInfo v | .thmInfo v | .opaqueInfo v
  | .ctorInfo v | .recInfo v | .inductInfo v => v.type
  | .quotInfo v => v.type

private def declarationValue? : ConstantInfo → Option Expr
  | .defnInfo v | .thmInfo v | .opaqueInfo v => some v.value
  | _ => none

/-- What a companion actually asserts.

A companion is written `def C.witness : Prop := ...`, so its *type* is the bare `Prop` and carries
no information. The assertion lives in the body. Reading the type instead of the body was the
original defect here, and `lake exe fidelity` caught it on this repository's own example. -/
private def assertion (info : ConstantInfo) : Expr :=
  (declarationValue? info).getD (declarationType info)

private def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | body => body

/-- A closed proposition: a `Prop`-valued declaration taking no mathematical input. A predicate
such as `IsReduced x` is terminology, not a claim, and is audited as a definition instead. -/
private def isClosedProposition (type : Expr) : Bool :=
  type.isProp && !type.isForall

/-- `True`, however spelled after instantiation. A companion of this shape is not evidence. -/
private def isTriviallyTrue (type : Expr) : Bool :=
  (forallBody type).getAppFn.constName? == some ``True

private def mentions (subject : Name) (type : Expr) : Bool :=
  Option.isSome <| type.find? fun e => e.constName? == some subject

/-- The companion must be *about* its subject. It counts as about the subject when it names the
subject directly, or when it shares a locally declared constant with the subject's own assertion.

The second clause is not slack, it is the common case: a satisfiability witness for
`∀ x, H x → C x` exhibits an `x` satisfying `H`, and so names `H` rather than the claim. Requiring
the claim's own name would reject exactly the right shape. Sharing is restricted to constants
declared in the statement modules, because sharing `Finset` or `Nat` with the subject would make
the check vacuous.

This rejects a companion about something else entirely. It does not certify that the companion is
the *right* evidence, which no check here can do; that stays on the semantic-review list. -/
private def isAbout (subject : Name) (local' : Std.HashSet Name)
    (subjectAssertion companionAssertion : Expr) : Bool :=
  mentions subject companionAssertion ||
    subjectAssertion.getUsedConstants.any fun c =>
      local'.contains c && mentions c companionAssertion

private structure Obligation where
  subject : Name
  companion : Name
  kind : String

private def audit (modules : Array Name) : CoreM (Array Obligation × Array String) := do
  let environment ← getEnv
  let moduleNames := environment.allImportedModuleNames
  let mut obligations := #[]
  let mut violations := #[]

  -- Names declared by the statement modules themselves. Sharing one of these with the subject is
  -- what makes a companion count as being about it.
  let mut local' : Std.HashSet Name := {}
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if let some owner := moduleNames[index.toNat]? then
        if modules.contains owner then
          local' := local'.insert name

  for moduleName in modules do
    let mut found := false
    for (name, info) in environment.constants.toList do
      if name.isInternal then
        continue
      let some index := environment.getModuleIdxFor? name | continue
      let some owner := moduleNames[index.toNat]? | continue
      if owner != moduleName then
        continue
      -- A companion is itself a declaration in this module; do not demand a companion of it.
      if name.getString! == "witness" || name.getString! == "separating" then
        continue

      let type := declarationType info
      let (suffix, kind) :=
        if isClosedProposition type then ("witness", "closed claim")
        else match info with
          | .defnInfo _ | .inductInfo _ => ("separating", "definition")
          | _ => ("", "")
      if kind == "" then
        continue
      found := true

      let companion := Name.mkStr name suffix
      match environment.checked.get.find? companion with
      | none =>
          violations := violations.push
            s!"{kind} {name} has no {companion}"
      | some companionInfo =>
          let companionType := assertion companionInfo
          if isTriviallyTrue companionType then
            violations := violations.push
              s!"{companion} is `True`, which is not evidence about {name}"
          else if !isAbout name local' (assertion info) companionType then
            violations := violations.push
              s!"{companion} does not mention {name}, so it is evidence about something else"
          else
            obligations := obligations.push ⟨name, companion, kind⟩

    if !found then
      violations := violations.push
        s!"{moduleName} is a reader-facing statement module but declares no claim or definition"

  return (obligations, violations)

/-- Import with environment extensions initialized; the environment is kept until this
short-lived process exits, as initializer results may point into its regions. -/
private unsafe def withImportedEnv {α} (modules : Array Name) (action : CoreM α) : IO α := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let imports := modules.map fun module => ({ module } : Import)
  let environment ← importModules imports {} (trustLevel := 1024)
    (leakEnv := true) (loadExts := true)
  Prod.fst <$> Core.CoreM.toIO
    (ctx := { fileName := "<fidelity>", fileMap := default })
    (s := { env := environment }) action

public unsafe def main : IO UInt32 := do
  let modules ← statementModules
  if modules.isEmpty then
    IO.eprintln "fidelity: no reader-facing statement modules found."
    return 1
  let (obligations, violations) ← withImportedEnv modules (audit modules)
  if !violations.isEmpty then
    IO.eprintln s!"fidelity: {violations.size} violation(s):"
    for violation in violations do
      IO.eprintln s!"  {violation}"
    return 1
  for obligation in obligations do
    IO.println s!"{obligation.kind} {obligation.subject} ← {obligation.companion}"
  IO.println s!"fidelity: {obligations.size} obligation(s) discharged; \
    every claim has a satisfiability witness and every definition a separating example."
  return 0
