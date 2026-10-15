import BakerHarman

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in this library and its imported analytic declarations,
including private and generated declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold
      (init := #[]) fun names name _ =>
    let publicName := privateToUserName name
    if (`BakerHarman).isPrefixOf publicName || (`OAI.Problem337).isPrefixOf publicName ||
        (`OAI.Erdos3).isPrefixOf publicName then
      names.push name
    else names
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} declarations; only propext, Classical.choice and Quot.sound found."
