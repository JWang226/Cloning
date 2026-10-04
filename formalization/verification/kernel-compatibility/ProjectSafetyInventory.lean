import Cloning
import Lean
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut moduleCount := 0
  let mut allNames : Array Name := #[]
  let mut seen := NameSet.empty
  let mut unsafeRecords : Array Json := #[]
  let mut partialRecords : Array Json := #[]
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!
    if moduleName == `Cloning || (`Cloning).isPrefixOf moduleName then
      if moduleName != `Cloning then
        moduleCount := moduleCount + 1
      let data := env.header.moduleData[index]!
      for name in data.constNames do
        let some info := env.find? name | throwError "Missing {name}"
        unless seen.contains name do
          seen := seen.insert name
          allNames := allNames.push name
          let kind := match info with
            | .axiomInfo _ => "axiom"
            | .defnInfo _ => "definition"
            | .thmInfo _ => "theorem"
            | .opaqueInfo _ => "opaque"
            | .quotInfo _ => "quotient"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
          let record := Json.mkObj [
            ("module", toJson moduleName.toString),
            ("name", toJson name.toString),
            ("kind", toJson kind),
            ("isUnsafe", toJson info.isUnsafe),
            ("isPartial", toJson info.isPartial)]
          if info.isUnsafe then
            unsafeRecords := unsafeRecords.push record
          if info.isPartial then
            partialRecords := partialRecords.push record
  liftIO <| IO.println ("PROJECT_SAFETY_INVENTORY " ++ (Json.mkObj [
    ("modules", toJson moduleCount),
    ("project_declarations", toJson allNames.size),
    ("declaration_names", toJson ((allNames.qsort Name.lt).map Name.toString)),
    ("unsafe_declarations", toJson unsafeRecords),
    ("partial_declarations", toJson partialRecords)]).compress)
