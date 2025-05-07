import Notes.Main
import VersoManual


open Verso.Genre.Manual

def main := manualMain (%doc Notes.Main) (config := config)
where config := {
    extraFiles := [("Static", "Static")],
    sourceLink := some "https://github.com/HEPLean/PhysLean",
    issueLink := some "https://github.com/HEPLean/PhysLean/issues",
    logo := some "/Static/Logo.svg"
}
