import UnforcedLeray
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx]!.module
    unless mod.toString.startsWith "UnforcedLeray" || mod.toString.startsWith "NonUniqueEuler" || mod.toString.startsWith "NavierStokes" do continue
    match info with
    | .axiomInfo _ => throwError "Project declares an axiom: {name}"
    | .thmInfo _ =>
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axioms}"
    | _ => pure ()
  logInfo m!"Audited {count} project theorems. This is not evidence that MainClaim is proved."
