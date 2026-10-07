import Cloning
import Lean.Util.CollectAxioms

open Lean Elab Command

private def sharedAuditWrite (handle : IO.FS.Handle) (value : Json) : IO Unit := do
  handle.putStrLn value.compress
  handle.flush

private def sharedAuditKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let handle ← liftIO <| IO.FS.Handle.mk "audit-native.jsonl" .write
  let importedModules := env.header.moduleNames.filter fun name =>
    name == `Cloning || (`Cloning).isPrefixOf name
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "begin"), ("audit_schema", toJson "cloning-shared-axiom-audit-v1"),
    ("source_manifest_sha256", toJson "1f104289b4452edb061871f37478b8b71052bb6643c9e3fde58bd65318e66883"),
    ("imported_modules", toJson importedModules.size)]
  let mut seen : NameSet := {}
  let mut roots : Array Name := #[]
  let mut exportOccurrences := 0
  let mut moduleCount := 0
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!
    if moduleName == `Cloning || (`Cloning).isPrefixOf moduleName then
      let data := env.header.moduleData[index]!
      let mut constants : Array Json := #[]
      let mut moduleSeen : NameSet := {}
      for name in data.constNames do
        if moduleSeen.contains name then
          throwError "Duplicate compiled export {name} within {moduleName}"
        moduleSeen := moduleSeen.insert name
        let some info := env.checked.get.find? name
          | throwError "Missing checked declaration {name} from {moduleName}"
        constants := constants.push <| Json.mkObj [
          ("name", toJson name.toString), ("kind", toJson (sharedAuditKind info)),
          ("private", toJson (name.toString.startsWith "_private."))]
        exportOccurrences := exportOccurrences + 1
        if !seen.contains name then
          seen := seen.insert name
          roots := roots.push name
      moduleCount := moduleCount + 1
      liftIO <| sharedAuditWrite handle <| Json.mkObj [
        ("event", toJson "module"), ("module", toJson moduleName.toString),
        ("constant_count", toJson constants.size), ("constants", Json.arr constants)]
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "inventory_complete"), ("imported_modules", toJson moduleCount),
    ("export_occurrences", toJson exportOccurrences), ("unique_roots", toJson roots.size)]
  -- One State, including its visited set, is shared across every unique root.
  -- The pinned native collector retains its exact type/value and cycle semantics.
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let axioms := state.axioms.map Name.toString
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "aggregate"), ("root_count", toJson roots.size),
    ("visited_constants", toJson state.visited.toList.length), ("axioms", toJson axioms)]
  let unexpected := axioms.filter fun name =>
    name != "Classical.choice" && name != "Quot.sound" && name != "propext"
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "complete"), ("passed", toJson unexpected.isEmpty)]
  if !unexpected.isEmpty then
    throwError "Unexpected aggregate axioms: {unexpected}"
