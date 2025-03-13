import Notes.Genre.Basic
import Notes.Main
import VersoManual
import Notes.Genre.Declaration


open Verso.Genre.Manual

def main := manualMain (%doc Notes.Main) (config := config)
where config := {
    sourceLink := some "https://github.com/HEPLean/PhysLean",
    issueLink := some "https://github.com/HEPLean/PhysLean/issues",
}
