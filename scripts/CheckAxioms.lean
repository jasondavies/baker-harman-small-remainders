import BakerHarman

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in this library and its imported analytic declarations,
selected by defining module, including declarations in other namespaces,
private declarations, and generated declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold
      (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`BakerHarman).isPrefixOf moduleName || (`BakerHarmanAnalytics).isPrefixOf moduleName then
        names.push name
      else names
    | none => names
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} declarations; only propext, Classical.choice and Quot.sound found."
