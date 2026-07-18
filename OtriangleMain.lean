import VersoManual
import VersoBlueprint.PreviewManifest
import Otriangle.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Otriangle.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
