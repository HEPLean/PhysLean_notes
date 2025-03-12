import Notes.Genre.Basic
import Notes.Main

def main (_ : List String) := PhysLeanNote.render "./Site" #[
    ⟨(%doc Notes.HarmonicOscillator), "HarmonicOscillator.html"⟩,
    ⟨(%doc Notes.WicksTheorem), "WicksTheorem.html"⟩
    ]
