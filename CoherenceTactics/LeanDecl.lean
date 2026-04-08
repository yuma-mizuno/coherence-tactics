import VersoManual

open Lean
open Verso Doc Elab Genre.Manual
open Verso.ArgParse
open Verso.Code.External
open SubVerso.Module

namespace CoherenceTactics

private def parseDeclNames (code : StrLit) : Array Name :=
  code.getString.splitOn "\n"
    |> List.toArray
    |> .map (fun s => String.trimAscii s |>.copy)
    |> .filter (not ∘ String.isEmpty)
    |> .map String.toName

private def findDeclItems (items : Array ModuleItem) (declName : Name) : Array ModuleItem :=
  let declName := declName.eraseMacroScopes
  items.filter fun item =>
    item.defines.any fun n => n.eraseMacroScopes == declName

private def isAnchorMarkerLine (hl : SubVerso.Highlighting.Highlighted) : Bool :=
  let s := (SubVerso.Highlighting.Highlighted.toString hl).trimAscii.toString
  String.startsWith s "-- ANCHOR:" || String.startsWith s "-- ANCHOR_END:"

private def stripAnchorMarkers
    (hl : SubVerso.Highlighting.Highlighted) : SubVerso.Highlighting.Highlighted :=
  (SubVerso.Highlighting.Highlighted.lines hl).foldl
    (init := SubVerso.Highlighting.Highlighted.empty)
    fun acc line =>
      if isAnchorMarkerLine line then acc else acc ++ line

set_option maxHeartbeats 2000000 in
@[code_block_expander leanAnchor]
def leanAnchor : CodeBlockExpander
  | args, _code => do
    if let some (Arg.anon a) := args[0]? then
      let cfg : CodeContext ←
        parseThe CodeContext (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1)
      let { module := moduleName, project, anchor?, showProofStates := _, defSite := _ } := cfg
      withAnchored project moduleName anchor? fun hl => do
        let hl := stripAnchorMarkers hl
        pure #[← ``(
          Verso.Code.External.ExternalCode.leanBlock
            (genre := Verso.Genre.Manual)
            $(quote hl)
            $(quote cfg.toCodeConfig))]
    else
      throwError "Expected a positional argument first (the anchor name)"

@[code_block_expander leanDecl]
def leanDecl : CodeBlockExpander
  | args, code => do
    let cfg : CodeModuleContext ← parseThe CodeModuleContext args
    let { module := moduleName, project, showProofStates := _, defSite := _ } := cfg
    let declNames := parseDeclNames code
    if declNames.isEmpty then
      throwErrorAt code "Expected at least one declaration name"
    let items ← loadModuleContent project moduleName.getId.toString
    let mut blocks := #[]
    for declName in declNames do
      let found := findDeclItems items declName
      if found.isEmpty then
        throwErrorAt code
          m!"Declaration '{declName}' not found in module '{moduleName.getId}'."
      if found.size = 1 then
        let some item := found[0]?
          | throwErrorAt code m!"Internal error while extracting '{declName}'."
        let itemCode := stripAnchorMarkers item.code
        blocks := blocks.push <| ← ``(
          Verso.Code.External.ExternalCode.leanBlock
            (genre := Verso.Genre.Manual)
            $(quote itemCode)
            $(quote cfg.toCodeConfig))
      else
        throwErrorAt code
          m!"Declaration '{declName}' was found in multiple command items in module '{moduleName.getId}'."
    pure blocks

end CoherenceTactics
