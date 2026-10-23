module

-- audit.py adds direct `import all` declarations for the local proof closure.
-- Direct imports retain private theorem helpers under Lean's module system.
import all Solution
meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command

@[expose] public section

/-! Audit the actual theorem dependencies in the generated proof environment.
The independent Challenge module has deliberate statement holes and must never
enter this environment. Mathematical scope is documented in docs/coverage.md. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  if env.header.moduleNames.contains `Challenge then
    throwError "The proof audit must not import Challenge"
  let isAuditedModule := fun name : Name =>
    name == `Solution || name.toString.startsWith "SpanningTreeIsoperimetry" ||
      name.toString.startsWith "SquareMaximality"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for owner in env.header.moduleNames do
    if isAuditedModule owner then
      logInfo m!"AUDIT_MODULE|{owner}"
  for (name, info) in env.constants.toList do
    match info with
    | .thmInfo _ =>
      let some idx := env.getModuleIdxFor? name | continue
      let owner := env.header.moduleNames[idx]!
      unless isAuditedModule owner do continue
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      logInfo m!"AUDIT|{owner}|{name}|{String.intercalate "," (axioms.toList.map Name.toString)}"
      checked := checked + 1
    | _ => pure ()
  if checked = 0 then throwError "No project theorems were audited"
  logInfo m!"AUDIT_COUNT|{checked}"
