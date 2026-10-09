import SpanningTreeIsoperimetry
import Lean.Util.CollectAxioms

/-! Audit declarations in the compiled environment, including private helpers.
This does not infer whole-paper completion from a declaration count. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    match info with
    | .thmInfo _ =>
      let some idx := env.getModuleIdxFor? name | continue
      let owner := env.header.moduleNames[idx]!
      unless owner.toString.startsWith "SpanningTreeIsoperimetry" ||
          owner.toString.startsWith "SquareMaximality" do continue
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      logInfo m!"AUDIT|{owner}|{name}|{String.intercalate "," (axioms.toList.map Name.toString)}"
      checked := checked + 1
    | _ => pure ()
  if checked = 0 then throwError "No project theorems were audited"
  logInfo m!"AUDIT_COUNT|{checked}"
