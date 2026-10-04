import Lean
open Lean
private partial def stripMetadata : Expr → Expr
  | .mdata _ e => stripMetadata e
  | .app f a => .app (stripMetadata f) (stripMetadata a)
  | .lam n t b bi => .lam n (stripMetadata t) (stripMetadata b) bi
  | .forallE n t b bi => .forallE n (stripMetadata t) (stripMetadata b) bi
  | .letE n t v b nd => .letE n (stripMetadata t) (stripMetadata v) (stripMetadata b) nd
  | .proj n i e => .proj n i (stripMetadata e)
  | e => e

def main (args : List String) : IO Unit := do
  let [rootsPath] := args | throw <| IO.userError "expected roots path"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Cloning }] {}
  for raw in (← IO.FS.readFile rootsPath).splitOn "\n" do
    if !raw.isEmpty then
      let some name := Syntax.decodeNameLit ("`" ++ raw) | throw <| IO.userError raw
      let some (.defnInfo info) := env.find? name | throw <| IO.userError s!"missing definition {raw}"
      IO.println <| Json.compress <| Json.mkObj [
        ("name", toJson raw),
        ("safety", toJson (reprStr info.safety)),
        ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("type_repr", toJson (reprStr (stripMetadata info.type))),
        ("value_repr", toJson (reprStr (stripMetadata info.value)))]
