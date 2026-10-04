import Cloning
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modName == `Cloning || (`Cloning).isPrefixOf modName then
      let data := env.header.moduleData[idx]!
      let inventory := Json.mkObj [
        ("module", toJson modName.toString),
        ("index", toJson idx),
        ("owner", toJson (idx % 3)),
        ("constant_names", toJson (data.constNames.map Name.toString))]
      liftIO <| IO.println ("SHARD_INVENTORY " ++ inventory.compress)
    if (modName == `Cloning || (`Cloning).isPrefixOf modName) && idx % 3 == 1 then
      let data := env.header.moduleData[idx]!
      liftIO <| IO.println ("MODULE_REPORT " ++ modName.toString)
      for name in data.constNames do
        let some info := env.find? name
          | throwError "Missing compiled declaration {name} from {modName}"
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let axioms ← collectAxioms name
        let report := Json.mkObj [
          ("module", toJson modName.toString),
          ("name", toJson name.toString),
          ("kind", toJson kind),
          ("private", toJson (name.toString.startsWith "_private.")),
          ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString))]
        liftIO <| IO.println ("AXIOM_REPORT " ++ report.compress)
        let allowed := #["propext", "Classical.choice", "Quot.sound"]
        let unexpected := axioms.filter (fun a => !allowed.contains a.toString)
        unless unexpected.isEmpty do
          throwError "Unexpected axioms in {name}: {unexpected}"
  liftIO <| IO.println ("SHARD_COMPLETE " ++ (Json.mkObj [("index", toJson (1 : Nat)), ("jobs", toJson (3 : Nat))]).compress)
