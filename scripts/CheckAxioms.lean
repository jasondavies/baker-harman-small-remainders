import BakerHarman

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in this library and its imported analytic declarations,
selected by defining module, including declarations in other namespaces,
private declarations, and generated declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- A source added outside the umbrella import graph must not escape the audit.
  let scriptDir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let repoRoot ← IO.FS.realPath (scriptDir / "..")
  for (directory, modulePrefix) in #[
      ("BakerHarman", `BakerHarman),
      ("vendor/baker-harman-analytics/BakerHarmanAnalytics", `BakerHarmanAnalytics)] do
    let sourceRoot := repoRoot / directory
    for path in (← sourceRoot.walkDir) do
      if path.extension == some "lean" then
        let parts := (path.withExtension "").components.drop sourceRoot.components.length
        let moduleName := parts.foldl Name.str modulePrefix
        unless env.header.moduleNames.contains moduleName do
          throwError "Source module is not imported by the audit: {moduleName}"
  -- Module tables avoid scanning every declaration imported from Mathlib.
  let mut names : Array Name := #[]
  for moduleName in env.header.moduleNames, moduleData in env.header.moduleData do
    if (`BakerHarman).isPrefixOf moduleName || (`BakerHarmanAnalytics).isPrefixOf moduleName then
      names := names ++ moduleData.constNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Share one visited set across roots; inspect theorem and opaque bodies too.
  let mut pending := names.map fun name => (name, name)
  let mut visited : NameSet := {}
  while let some (origin, name) := pending.back? do
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      let some info := env.checked.get.find? name
        | throwError "Missing declaration {name} while auditing {origin}"
      if info.isAxiom && !allowed.contains name then
        throwError "Unexpected axiom {name} in {origin}"
      let mut dependencies := info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        dependencies := dependencies ++ value.getUsedConstants
      if let .inductInfo value := info then
        dependencies := dependencies ++ value.ctors.toArray
      for dependency in dependencies do
        pending := pending.push (origin, dependency)
  let analyticCount := names.filter fun name =>
    match env.getModuleIdxFor? name with
    | some idx => (`BakerHarmanAnalytics).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  logInfo m!"Audited {names.size} declarations ({analyticCount.size} analytics); only propext, Classical.choice and Quot.sound found."
