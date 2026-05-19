/-
Mathgame — declaration-level (logical) dependency edges for this workspace.

  lake exe mathgame-deps

Directed **dependency → dependent**: if body/type of `to` mentions constant `from`,
we emit {"from":"…","to":"…"}. Mathlib / Lean / Std / Init / Lake / Cli are excluded.

Stdout: { "logicalEdges": [ {"from":"…","to":"…"}, … ] }
-/

import Lean
import Main

open Lean

private def isExternalModule (modStr : String) : Bool :=
  modStr.startsWith "Mathlib." ||
  modStr.startsWith "Lean." ||
  modStr.startsWith "Init." ||
  modStr.startsWith "Std." ||
  modStr.startsWith "Lake." ||
  modStr.startsWith "Cli." ||
  modStr.startsWith "Plausible." ||
  modStr.startsWith "Cache." ||
  modStr.startsWith "ProofWidgets."

private def isProjectConstant (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | none => false
  | some mod => !isExternalModule mod.toString

private partial def jsonEscape (s : String) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < s.length then
      let c := s.get ⟨i⟩
      let acc' :=
        if c == '"' then acc ++ "\\\""
        else if c == '\\' then acc ++ "\\\\"
        else acc.push c
      go (i + 1) acc'
    else acc
  go 0 ""

private unsafe def collectPairs (env : Environment) : List (String × String) :=
  Id.run do
    let mut acc : List (String × String) := []
    let allConsts := env.constants.map₁.toList ++ env.constants.map₂.toList
    for (n, ci) in allConsts do
      if !isProjectConstant env n then continue
      let deps := ci.getUsedConstantsAsSet
      for d in deps do
        if d != n && isProjectConstant env d then
          acc := (d.toString, n.toString) :: acc
    return acc

private unsafe def emitJson (env : Environment) : IO Unit := do
  let raw := collectPairs env
  let esc (p : String × String) :=
    s!"{{\"from\":\"{jsonEscape p.1}\",\"to\":\"{jsonEscape p.2}\"}}"
  let inner := String.intercalate "," (raw.map esc)
  IO.println s!"{{\"logicalEdges\":[{inner}]}}"

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Main}] Options.empty 0
  emitJson env
  return 0
