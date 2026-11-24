import UnforcedLeray
import Lean.Elab.Command
import Lean.Util.CollectAxioms

example : UnforcedLeray.MainClaim := UnforcedLeray.main_theorem

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let name := `UnforcedLeray.main_theorem
  match env.find? name with
  | some (.thmInfo _) => pure ()
  | _ => throwError "{name} is not a theorem declaration"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: {axioms}"
