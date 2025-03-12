/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Tooby-Smith
-/
import Verso
/-!

## Genre for PhysLean notes

## Note on adaptation

The material here has been adapted from Verso. The original code can be found at
https://github.com/leanprover/verso
The original code is licensed under the Apache 2.0 license, and the copyright is held by the
Lean FRO LLC.
-/



namespace PhysLeanNote
open Lean

inductive BlockDocstring where
  | name : Name → BlockDocstring

/-- Each part can be tagged with meta-data. -/
structure PartMetadata where
  tag : String

/-- A link to a given tag -/
structure SectionRef where
  /-- The section being referred to -/
  dest : String
  /--
  A unique tag used for back-references. The system itself is expected to fill this out during
  the traversal pass.
  -/
  tag : Option Nat := none


structure TraverseContext where
  URL : String

structure TraverseState where
  /-- A mapping from header IDs to incoming link IDs -/
  refTargets : Std.HashMap String (Std.HashSet Nat) := {}

  /-- All the part tags in the document -/
  partTags : Std.HashSet String := {}

  /-- The next unique link tag to assign -/
  nextLinkTag : Nat := 0

def hashMapEqBy [BEq α] [Hashable α] (eq : β → β → Bool) (xs ys : Std.HashMap α β) : Bool :=
    xs.size == ys.size &&
    xs.fold (fun soFar k v => soFar && (ys[k]? |>.map (eq v) |>.getD false)) true

def hashSetEq [BEq α] [Hashable α] (xs ys : Std.HashSet α) : Bool :=
    xs.size == ys.size &&
    xs.fold (fun soFar x => soFar && ys.contains x) true

instance : BEq TraverseState where
  beq st1 st2 :=
    hashMapEqBy hashSetEq st1.refTargets st2.refTargets &&
    hashSetEq st1.partTags st2.partTags &&
    st1.nextLinkTag == st2.nextLinkTag


end PhysLeanNote

open Verso Doc

def PhysLeanNote : Genre where
  Inline := PhysLeanNote.SectionRef
  Block := PhysLeanNote.BlockDocstring
  PartMetadata := PhysLeanNote.PartMetadata
  TraverseContext := PhysLeanNote.TraverseContext
  TraverseState := PhysLeanNote.TraverseState

namespace PhysLeanNote

abbrev TraverseM := ReaderT TraverseContext (StateT TraverseState Id)

def renderBlockDocstring (doc : BlockDocstring) : String :=
  match doc with
  | BlockDocstring.name n => "Name: " ++ n.toString

instance : TraversePart PhysLeanNote := {}

instance : Traverse PhysLeanNote TraverseM where
  part _ := pure none
  block b :=  pure ()
  inline _ := pure ()
  genrePart metadata _ := do
    -- Save the found tag so it can be used for cross-reference lints later on
    modify fun st =>
      {st with partTags := st.partTags.insert metadata.tag}
    -- Returning `none` means that the document AST is unmodified
    pure none
  genreBlock _ _ := pure none
  genreInline
    -- Dates will be handled later, at HTML generation
    -- If the outgoing link has no ID, assign one
    | ⟨dest, none⟩, contents => do
      let t ← modifyGet fun st => (st.nextLinkTag, {st with nextLinkTag := st.nextLinkTag + 1})
      pure (some (.other ( ⟨dest, some t⟩) contents))
    -- Remember the pointer from the outgoing link to its target
    | ⟨dest, some t⟩, _ => do
      modify fun st =>
        {st with
          refTargets := st.refTargets.insert dest (st.refTargets.getD dest .empty |>.insert t)}
      pure none

open Verso.Output Html

instance : GenreHtml PhysLeanNote IO where
  -- When rendering a part to HTMl, extract the incoming links from the final traversal state and
  -- insert back-references
  part recur metadata | (.mk title titleString _ content subParts) => do
    let incoming := (← HtmlT.state).refTargets[metadata.tag]?
    let content' := if let some i := incoming then
      let links := i.toArray.map fun t => ListItem.mk #[Doc.Block.para #[Doc.Inline.link #[.text "(link)"] s!"#link-{t}"]]
      #[Doc.Block.para #[.text "Incoming links:"], Doc.Block.ul links] ++ content
    else content
    -- It's important that this not include the metadata in the recursive call, or the generator
    -- will loop (the metadata's presence is what triggers the call to `GenreHtml.part`)
    let part' := .mk title titleString none content' subParts
    recur part' (fun lvl title => .tag s!"h{lvl}" #[("id", metadata.tag)] title)
  -- There are no genre-specific blocks, so no code is needed here
  block _ _ blkExt _ := do pure (renderBlockDocstring blkExt)
  inline recur
    |  ⟨dest, none⟩, contents => do
      HtmlT.logError s!"No ID assigned to section link of {dest}"
      pure {{<a href=s!"#{dest}"> {{← contents.mapM recur}} </a>}}
    -- Otherwise emit the right ID
    |  ⟨dest, some t⟩, contents => do
      pure {{<a href=s!"#{dest}" id=s!"link-{t}"> {{← contents.mapM recur}} </a>}}

structure PageParameters where
  part : Part PhysLeanNote
  url : String
/--
Rendering an individual page.
-/
def renderPage (dir : String) (page : PageParameters) : IO UInt32 := do
  let mut doc := page.1
  -- Do the traversal pass until either too many iterations have been reached (indicating a bug) or
  -- a fixed point is reached
  let mut state : PhysLeanNote.TraverseState := {}
  let context : PhysLeanNote.TraverseContext := {URL := "https://physlean.com"}
  let mut iterations := 0
  repeat
    IO.println s!"Iteration {iterations} of the traversal pass"
    if iterations > 10 then
      throw <| IO.userError s!"Failed to traverse the document after {iterations} iterations. The genre is likely buggy."
    let (doc', state') := PhysLeanNote.traverse doc |>.run context |>.run state
    if state == state' then break
    state := state'
    doc := doc'
    iterations := iterations + 1
  IO.println s!"Traversal completed after {iterations} iterations"

  -- Render the resulting document to HTML. This requires a way to log errors.
  let hadError ← IO.mkRef false
  let logError str := do
    hadError.set true
    IO.eprintln str

  IO.println "Rendering HTML"
  -- toHtml returns both deduplicated hover contents and the actual content.
  -- Since we're not rendering Lean code, we can ignore the hover contents.
  let (content, _) ← PhysLeanNote.toHtml {logError} context state {} {} {} doc .empty
  let html := {{
    <html>
      <head>
        <title>{{doc.titleString}}</title>
        <meta charset="utf-8"/>
      </head>
      <header style="background-color: #2C3E50; color: white; padding: 15px 0; width: 100%; box-shadow: 0 2px 4px rgba(0,0,0,0.1); margin-bottom: 20px;">
      <div style="width: 90%; margin: 0 auto; padding: 0 20px;">
        <h3 style="margin: 0; font-size: 1.5em; text-align: center;">{{ "PhysLean: Curated Notes" }}</h3>
      </div>
    </header>
      <body style="max-width: 800px; margin: 0 auto; padding: 40px; font-family: 'Times New Roman', Times, serif; line-height: 1.5; color: #333; text-align: justify;">{{ content }}</body>
    </html>
  }}

  IO.println "Writing to html file"
  IO.FS.withFile (dir ++ "/" ++ page.2) .write fun h => do
    h.putStrLn html.asString

  if (← hadError.get) then
    IO.eprintln "Errors occurred while rendering"
    pure 1
  else
    pure 0

def render (dir : String) (pages : Array (PageParameters)) : IO UInt32 := do
  let _ ← pages.mapM fun x => renderPage dir x
  pure 0

end PhysLeanNote

def sectionRef (content : Array (Inline PhysLeanNote)) (dest : String) : Inline PhysLeanNote :=
  .other ({dest}) content

def docString (n : String) : Block PhysLeanNote :=
  .other (PhysLeanNote.BlockDocstring.name n.toName) #[]
