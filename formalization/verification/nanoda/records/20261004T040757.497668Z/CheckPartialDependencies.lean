import Cloning
import Lean
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`Cloning.MultimodeCoherent.numberIterate._unsafe_rec,`Cloning.PBW.errorTerms._unsafe_rec,`Cloning.PBW.gramConstant._unsafe_rec,`Cloning.PBW.occupationFactorial._unsafe_rec,`Cloning.PBW.removeOne._unsafe_rec,`Cloning.PBW.wick._unsafe_rec,`Cloning.PBW.word._unsafe_rec,`Cloning.TensorLie.highestAction._unsafe_rec,`Cloning.TensorLie.loweringHeight._unsafe_rec,`Cloning.TensorLie.loweringOperator._unsafe_rec,`Cloning.TensorLie.loweringScale._unsafe_rec,`Cloning.TensorLie.loweringSplits._unsafe_rec,`Cloning.TensorLie.loweringWeight._unsafe_rec,`Cloning.TensorLie.loweringWord._unsafe_rec,`Cloning.TensorLie.physicalSectorListSpan._unsafe_rec,`Cloning.TensorLie.recursivePhysicalDecomposition._unsafe_rec,`Cloning.TensorLie.rootInversions._unsafe_rec,`Cloning.TensorLie.rootOccupationSplits._unsafe_rec,`Cloning.YoungGeneral.shapeAdd._unsafe_rec,`Cloning.YoungGeneral.shapeRemovable._unsafe_rec,`Cloning.YoungGeneral.tableauInsert._unsafe_rec,`Cloning.YoungGeneral.tableauRemovable._unsafe_rec,`Cloning.YoungGeneral.tableauReverse._unsafe_rec,`Cloning.YoungTwoRow.Path._unsafe_rec,`Cloning.YoungTwoRow.legal._unsafe_rec,`Cloning.YoungTwoRow.lowerRow._unsafe_rec,`Cloning.YoungTwoRow.pathFintype._unsafe_rec,`Cloning.YoungTwoRow.spin._unsafe_rec,`Cloning.YoungTwoRow.upperRow._unsafe_rec,`Cloning.YoungTwoRow.weight._unsafe_rec]
  let mut scanned := 0
  let mut matchCount := 0
  for (name, info) in env.constants.toList do
    if !info.isUnsafe && !info.isPartial then
      scanned := scanned + 1
      let mut typeRefs : Array String := #[]
      let mut valueRefs : Array String := #[]
      for dep in info.type.getUsedConstants do
        if targets.contains dep then
          typeRefs := typeRefs.push dep.toString
      if let some value := info.value? true then
        for dep in value.getUsedConstants do
          if targets.contains dep then
            valueRefs := valueRefs.push dep.toString
      if !typeRefs.isEmpty || !valueRefs.isEmpty then
        matchCount := matchCount + 1
        liftIO <| IO.println ("SAFE_PARTIAL_REFERENCE " ++ (Json.mkObj [
          ("name", toJson name.toString),
          ("type_refs", toJson typeRefs),
          ("value_refs", toJson valueRefs)]).compress)
  for target in targets do
    let some info := env.find? target | throwError "Missing {target}"
    let refs := info.type.getUsedConstants.toList ++ ((info.value? true).toList.flatMap (fun value => value.getUsedConstants.toList))
    liftIO <| IO.println ("PARTIAL_DECLARATION " ++ (Json.mkObj [
      ("name", toJson target.toString),
      ("isUnsafe", toJson info.isUnsafe),
      ("isPartial", toJson info.isPartial),
      ("dependencies", toJson (refs.map Name.toString))]).compress)
  liftIO <| IO.println ("PARTIAL_DEPENDENCY_SUMMARY " ++ (Json.mkObj [
    ("safe_constants_scanned", toJson scanned),
    ("safe_constants_referencing_target_partials", toJson matchCount)]).compress)
