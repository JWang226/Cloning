import Lean

open Lean

/- This preparation check compares explicit theorem types after removing source
metadata, as the pinned exporter does. It does NOT replay proof terms, check
axiom dependencies, or replace Comparator. Run inside the prepared wrapper. -/
private partial def withoutMetadata : Expr → Expr
  | .mdata _ e => withoutMetadata e
  | .app f a => .app (withoutMetadata f) (withoutMetadata a)
  | .lam n t b bi => .lam n (withoutMetadata t) (withoutMetadata b) bi
  | .forallE n t b bi => .forallE n (withoutMetadata t) (withoutMetadata b) bi
  | .letE n t v b nd => .letE n (withoutMetadata t) (withoutMetadata v) (withoutMetadata b) nd
  | .proj n i e => .proj n i (withoutMetadata e)
  | e => e

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "config.json")
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  if names.isEmpty then throw <| IO.userError "empty theorem list"
  let challenge ← importModules #[{ module := `Challenge }] {}
  let solution ← importModules #[{ module := `Solution }] {}
  for rawName in names do
    let some name := Syntax.decodeNameLit ("`" ++ rawName)
      | throw <| IO.userError s!"invalid theorem name: {rawName}"
    let some (.thmInfo lhs) := challenge.find? name
      | throw <| IO.userError s!"challenge theorem missing: {name}"
    let some (.thmInfo rhs) := solution.find? name
      | throw <| IO.userError s!"solution theorem missing: {name}"
    if lhs.levelParams != rhs.levelParams || withoutMetadata lhs.type != withoutMetadata rhs.type then
      throw <| IO.userError s!"explicit statement differs: {name}"
  IO.println s!"Matched {names.size} explicit theorem types; no kernel replay performed."
