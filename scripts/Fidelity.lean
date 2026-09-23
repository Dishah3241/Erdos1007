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

* `C.drop_<h>` — for each non-dependent `Prop`-valued binder `h` of `C`'s body, a companion
  whose body is definitionally `¬ C'`, where `C'` is `C` with that binder removed. `<h>` is the
  binder's user name, or its 0-based index in the telescope when the binder is anonymous. A
  hypothesis written with `→` is anonymous: Lean stores it under a hygienic name. A binder is
  dependent when a later binder's type or the conclusion mentions it. Those cannot be removed,
  so the audit skips them and prints that. The proof `C.drop_<h>.proof`, in the proof sibling,
  is the kernel-checked counterexample.

and for every definition `D` in such a module:

* `D.separating` — a nondegenerate example distinguishing `D` from the nearest plausible wrong
  definition. Compilation does not establish that `IsRegular` means regular.

A witness or separating example must mention the declaration it is about, and must not be `True`.
That catches the obvious way to satisfy this audit without doing the work:
`theorem C.witness : True := trivial`. A drop companion is not checked that way. Definitional
equality with `¬ C'` is the check, and that negation may itself be `True`.

What this audit does *not* do: derive the witness, or try to prove the negation of `C`. Negation
stays human-directed, per `docs/PLAYBOOK.md` stage 1.

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

/-- Declarations this audit requires of a subject, rather than subjects themselves. -/
private def isObligationCompanion (declName : Name) : Bool :=
  match declName with
  | .str _ component =>
      component == "witness" || component == "separating" || component.startsWith "drop_"
  | _ => false

/-- Tag used in `C.drop_<tag>`. A name the user wrote is kept. A binder with no such name —
`Name.anonymous`, `_`, or the hygienic name Lean invents for `→` — uses its 0-based telescope
index, which is stable for two hypotheses the elaborator would otherwise both call `a`. -/
private def binderTag (userName : Name) (index : Nat) : String :=
  if userName.isAnonymous || userName.hasMacroScopes || userName == `_ then
    toString index
  else
    let tag := userName.toString
    if tag.isEmpty then toString index else tag

/-- A `Prop`-valued binder is dependent when a later binder's type or the conclusion mentions it.
Removing it would not be a well-formed proposition. -/
private def isDependentBinder (binders : Array Expr) (conclusion : Expr) (index : Nat) :
    MetaM Bool := do
  let fvarId := binders[index]!.fvarId!
  if conclusion.containsFVar fvarId then
    return true
  let mut dependent := false
  for j in [index + 1:binders.size] do
    let later ← binders[j]!.fvarId!.getDecl
    if later.type.containsFVar fvarId then
      dependent := true
  return dependent

/-- For each non-dependent `Prop` binder of `body`, require `claim.drop_<tag>` definitionally
equal to the negation of `body` with that binder removed. -/
private def checkHypothesisDrops (claim : Name) (body : Expr) :
    MetaM (Array Obligation × Array String × Array String) := do
  Meta.forallTelescope body fun binders conclusion => do
    let mut obligations : Array Obligation := #[]
    let mut violations : Array String := #[]
    let mut skips : Array String := #[]
    for index in [:binders.size] do
      let decl ← binders[index]!.fvarId!.getDecl
      -- `Meta.isProp`, not `Expr.isProp`: the binder's type is a proposition, not the sort `Prop`.
      unless ← Meta.isProp decl.type do
        continue
      let tag := binderTag decl.userName index
      if ← isDependentBinder binders conclusion index then
        skips := skips.push s!"skipped dependent binder {tag} of {claim}"
        continue
      let mut kept : Array Expr := #[]
      for j in [:binders.size] do
        if j != index then
          kept := kept.push binders[j]!
      let weakened ← Meta.mkForallFVars kept conclusion
      let negated := mkApp (mkConst ``Not) weakened
      let companion := Name.mkStr claim s!"drop_{tag}"
      match (← getEnv).checked.get.find? companion with
      | none =>
          violations := violations.push
            s!"closed claim {claim} has no {companion} for hypothesis {tag}"
      | some companionInfo =>
          let companionBody := assertion companionInfo
          let defEq ← withoutModifyingState (Meta.isDefEq companionBody negated)
          if defEq then
            obligations := obligations.push ⟨claim, companion, "hypothesis drop"⟩
          else
            violations := violations.push
              s!"{companion} is not definitionally the negation of {claim} \
                with hypothesis {tag} removed"
    return (obligations, violations, skips)

private def audit (modules : Array Name) :
    MetaM (Array Obligation × Array String × Array String) := do
  let environment ← getEnv
  let moduleNames := environment.allImportedModuleNames
  let mut obligations := #[]
  let mut violations := #[]
  let mut skips := #[]

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
      if isObligationCompanion name then
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

      if isClosedProposition type then
        let (dropObligations, dropViolations, dropSkips) ←
          checkHypothesisDrops name (assertion info)
        obligations := obligations ++ dropObligations
        violations := violations ++ dropViolations
        skips := skips ++ dropSkips

    if !found then
      violations := violations.push
        s!"{moduleName} is a reader-facing statement module but declares no claim or definition"

  return (obligations, violations, skips)

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
  let (obligations, violations, skips) ←
    withImportedEnv modules (Meta.MetaM.run' (audit modules))
  if !violations.isEmpty then
    IO.eprintln s!"fidelity: {violations.size} violation(s):"
    for violation in violations do
      IO.eprintln s!"  {violation}"
    return 1
  for obligation in obligations do
    IO.println s!"{obligation.kind} {obligation.subject} ← {obligation.companion}"
  for skip in skips do
    IO.println skip
  IO.println s!"fidelity: {obligations.size} obligation(s) discharged; \
    every claim has a satisfiability witness, every non-dependent hypothesis a drop \
    companion, and every definition a separating example."
  return 0
