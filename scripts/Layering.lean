/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean

/-!
# Audit the mathematical order of the source tree

General mathematics never imports a subject module, and a subject module never imports a later
subject stage. Examples, standalone entry points, and local test modules are leaves. Imports are
read from compiled artifacts.

`subjectRoots` is the project's own layering, ordered from earliest to latest stage; edit it when
the project's mathematical spine changes. `generalRoots` mirrors Mathlib's top-level areas and
should rarely need editing.
-/

open Lean

private def auditedRoot : Name := `Erdos1007

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

/-- General mathematics, mirroring Mathlib's top-level areas. Layer 0. -/
private def generalRoots : Array Name := #[
  `Erdos1007.Algebra,
  `Erdos1007.Analysis,
  `Erdos1007.Combinatorics,
  `Erdos1007.Data,
  `Erdos1007.FieldTheory,
  `Erdos1007.LinearAlgebra,
  `Erdos1007.NumberTheory,
  `Erdos1007.Order,
  `Erdos1007.RingTheory,
  `Erdos1007.SetTheory,
  `Erdos1007.Topology,
]

/-- The project's own mathematical spine, ordered earliest stage first. A module in stage `i`
may import stage `j` only when `j ≤ i`. Edit this when the spine changes. -/
private def subjectRoots : Array (Name × String) := #[
  (`Erdos1007.Geometry, "unit-distance geometry"),
  (`Erdos1007.Extremal, "extremal graph theory"),
]

private def leafRoots : Array Name := #[
  `Erdos1007.Examples,
  `Erdos1007.Standalone,
]

private def isLocalTest (name : Name) : Bool :=
  name.components.contains `Tests

private def leafRank? (name : Name) : Option Nat :=
  if isLocalTest name then
    some leafRoots.size
  else
    leafRoots.findIdx? (·.isPrefixOf name)

private def layerOf? (name : Name) : Option (Nat × String) :=
  if (leafRank? name).isSome then
    none
  else if generalRoots.any (·.isPrefixOf name) then
    some (0, "general mathematics")
  else
    (subjectRoots.findIdx? (fun (root, _) => root.isPrefixOf name)).map
      (fun index => (index + 1, subjectRoots[index]!.2))

/-- The forbidden direction, if this import crosses a stage boundary backwards. -/
private def crossesLayer (importer imported : Name) : Option String := do
  let (importerRank, importerLayer) ← layerOf? importer
  let (importedRank, importedLayer) ← layerOf? imported
  if importerRank < importedRank then
    some s!"{importerLayer} imports later stage {importedLayer}"
  else
    none

private def moduleImports (name : Name) : IO (Array Name) := do
  let olean ← findOLean name
  if !(← olean.pathExists) then
    throw <| IO.userError s!"layering: no compiled artifact for {name}; run `lake build` first."
  let (moduleData, _region) ← readModuleData olean
  return moduleData.imports.map (·.module)

public def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← collectLeanModules (auditedRoot.toString : System.FilePath)
  let mut violations := #[]
  let mut edges := 0
  for importer in modules do
    for imported in ← moduleImports importer do
      if !auditedRoot.isPrefixOf imported then
        continue
      edges := edges + 1
      if let some direction := crossesLayer importer imported then
        violations := violations.push s!"  {direction}: {importer} imports {imported}"
      if let some importedRank := leafRank? imported then
        if !(leafRank? importer).any (importedRank ≤ ·) then
          violations := violations.push
            s!"  leaf modules are imported backwards: {importer} imports {imported}"
  if modules.isEmpty then
    IO.eprintln "layering: no modules found."
    return 1
  if violations.isEmpty then
    IO.println s!"layering: {edges} project import(s) across {modules.size} modules \
      respect mathematical ownership; examples, standalone modules, and tests are leaves."
    return 0
  IO.eprintln s!"layering: {violations.size} violation(s):"
  for violation in violations do
    IO.eprintln violation
  return 1
