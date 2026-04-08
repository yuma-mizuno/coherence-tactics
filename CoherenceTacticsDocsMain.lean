import CoherenceTactics.Docs
import VersoManual

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main (args : List String) : IO UInt32 := do
  manualMain (%doc CoherenceTactics.Docs) (options := args) (config := { config with })
