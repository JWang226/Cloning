import Export

open Lean

/- A file-based front end to the unmodified, pinned lean4export API.  The
exporter's ordinary command line cannot portably hold all project roots.
This changes only where the root names come from; dumpConstant recursively
exports their dependencies exactly as in upstream Main.lean. -/
def main (args : List String) : IO Unit := do
  let [rootsPath] := args
    | throw <| IO.userError "expected one roots.txt path"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Cloning }] {}
  let contents ← IO.FS.readFile rootsPath
  let mut roots : Array Name := #[]
  for line in contents.splitOn "\n" do
    if !line.isEmpty then
      let some name := Syntax.decodeNameLit ("`" ++ line)
        | throw <| IO.userError s!"invalid root name: {line}"
      if (env.find? name).isNone then
        throw <| IO.userError s!"missing root declaration: {name}"
      roots := roots.push name
  if roots.isEmpty then
    throw <| IO.userError "refusing an empty root list"
  M.run env do
    initState env []
    dumpMetadata
    for name in roots do
      modify fun state => { state with noMDataExprs := {} }
      dumpConstant name
