/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Std.Data.HashSet
import VersoManual.Docstring
import PhysLean.Meta.Basic
import PhysLean.Meta.Remark.Properties
import PhysLean.Meta.Notes.ToHTML
/-!

## Note on adaptation

The material here has been adapted from Verso. The original code can be found at
https://github.com/leanprover/verso,
in particular from
https://github.com/leanprover/verso/blob/main/src/verso-manual/VersoManual/Docstring.lean

The original code is licensed under the Apache 2.0 license, and the copyright is held by the
Lean FRO LLC, and written primarly by David Thrane Christiansen.

The adaptation carried out is to change `{docstring ...}` in the Manual genre to
something more similar to a definition or lemma in a paper.

-/





open Lean hiding HashSet
open Std (HashSet)

open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse
open Verso.Code.Highlighted.WebAssets
set_option linter.unusedVariables false
open SubVerso.Highlighting

namespace Verso.Genre.Manual

namespace Block

structure DeclarationInfo where
  isDef : Bool
  isThm : Bool
deriving ToJson, FromJson

instance : Quote DeclarationInfo where
  quote := fun x =>
    match x with
    | { isDef := isDef, isThm := isThm } => Lean.Syntax.mkCApp `Verso.Genre.Manual.Block.DeclarationInfo.mk #[quote isDef, quote isThm]


/-- Given a name, returns the source code defining that name, including doc strings. -/
def getDeclString (name : Name) : CoreM String := do
  let env ← getEnv
  match ← findDeclarationRanges? name with
  | some { range := { pos, endPos, .. }, .. } =>
    match env.getModuleFor? name with
    | some fileName =>
      let fileContent ← IO.FS.readFile (".lake/packages/PhysLean/" ++ (fileName.toRelativeFilePath.toString.replace "./" ""))
      let fileMap := fileContent.toFileMap
      return fileMap.source.extract (fileMap.ofPosition pos) (fileMap.ofPosition endPos)
    | none => return ""
  | none => return ""

/-- Given a name, returns the source code defining that name,
  starting with the def ... or lemma... etc. -/
def getDeclStringNoDoc (name : Name) : CoreM String := do
  let declerationString ← getDeclString name
  let headerLine (line : String) : Bool :=
    line.startsWith "def " ∨ line.startsWith "lemma " ∨ line.startsWith "inductive "
    ∨ line.startsWith "structure " ∨ line.startsWith "theorem "
    ∨ line.startsWith "instance " ∨ line.startsWith "abbrev " ∨
    line.startsWith "noncomputable def " ∨ line.startsWith "noncomputable abbrev "
  let lines := declerationString.splitOn "\n"
  match lines.findIdx? headerLine with
  | none => panic! s!"{name} has no header line"
  | some i => return String.intercalate "\n" (lines.drop i)

def DeclarationInfo.ofName (n : Name) : MetaM DeclarationInfo := do
  let line ← Name.lineNumber n
  let fileName ← Name.fileName n
  let declString ← getDeclStringNoDoc n
  let constInfo ← getConstInfo n
  let isDef := constInfo.isDef ∨ Lean.isStructure (← getEnv) n ∨ constInfo.isInductive
  let isThm := declString.startsWith "theorem" ∨ declString.startsWith "noncomputable theorem"

  pure { isDef := isDef, isThm := isThm }

def declaration (name : Name) (declType : Docstring.DeclType) (declInfo : DeclarationInfo)
    (signature : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.declaration
  data := ToJson.toJson (name, declType, declInfo, signature)


end Block

open Verso.Doc.Elab

@[block_role_expander declaration]
def declaration : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← Elab.realizeGlobalConstNoOverloadWithInfo x
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
      let blockStx ←
        match ← Lean.findDocString? (← getEnv) name with
        | none => logWarningAt x m!"No docs found for '{x}'"; pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs
            | throwErrorAt x "Failed to parse docstring as Markdown"

          ast.blocks.mapM (blockFromMarkdownWithLean [name])

      if Lean.Linter.isDeprecated (← getEnv) name then
        logInfoAt x m!"'{x}' is deprecated"

      let declType ← Block.Docstring.DeclType.ofName name

      let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature name
      let tt := Lean.Widget.TaggedText.prettyTagged (w := 48) fmt
      let ctx := {
        env           := (← getEnv)
        mctx          := (← getMCtx)
        options       := (← getOptions)
        currNamespace := (← getCurrNamespace)
        openDecls     := (← getOpenDecls)
        fileMap       := default
        ngen          := (← getNGen)
      }
      let sig := Lean.Widget.tagCodeInfos ctx infos tt
      let signature ← some <$> renderTagged none sig ⟨{}, false⟩
      let extras ← getExtras name declType
      let declInfo ← Block.DeclarationInfo.ofName name
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.declaration $(quote name) $(quote declType)
        $(quote declInfo) $(quote signature)) #[$(blockStx ++ extras),*])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"
where
  getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor _ fieldInfo parents _ => do
      let ctorRow : Term ← do
        let header := if isClass then "Instance Constructor" else "Constructor"
        let sigDesc ←
          if let some docs := constructor.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure #[]
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])
      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "Extends"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])


      let fieldsRow : Term ← do
        let header := if isClass then "Methods" else "Fields"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs := i.docString? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
            else
              pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])
      /- Removing the below to get rid of field rows. -/
      -- pure <| #[ctorRow] ++ parentsRow.toArray ++ [fieldsRow]
      pure #[]
    | .inductive ctors .. => do
      let ctorSigs : Array Term ←
        -- Elaborate constructor docs in the type's NS
        ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
          let sigDesc ←
            if let some docs := c.docstring? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
    | _ => pure #[]



def declarationStyle := r#"
.namedocs {
  position: relative;
  border: solid 2px #99b3c0;
  background-color: #99b3c0;
  padding-left: 1px;
  padding-right: 1px;
  padding-bottom: 1px;
  padding-top: 1.5rem;
  margin-bottom: 1rem;
}

.namedocs .text {
  background-color: white;
  padding: 1.5rem;
  margin-top: 0.5rem;
}

.namedocs .text > pre {
  overflow-x: auto;
}

.namedocs .signature {
  font-family: var(--verso-code-font-family);
  font-size: larger;
  margin-top: 0 !important;
  margin-left: 1.5rem !important;
  margin-right: 1.5rem;
}

.namedocs .label {
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
  position: absolute;
  right: 0.5rem;
  top: 0.5rem;
}

/* Sticking content into the right margin is not good on narrow screens,
   so move the label to the left to make space for the permalink widget. */

@media screen and (max-width: 700px) {
  .namedocs:has(.permalink-widget.block) .label {
    right: 1.5rem;
  }
}

.namedocs h1 {
  font-size: 1rem;
  font-weight: bold;
}


.namedocs > .text .constructor {
  padding-left: 0.5rem;
  padding-top: 0;
  padding-right: 0;
  padding-bottom: 0;
  margin-top: 0.5rem;
  margin-bottom: 1.5rem;
}

.namedocs > .text .constructor::before {
  content: '| ';
  display: block;
  font-family: var(--verso-code-font-family);
  font-weight: bold;
  float: left;
  width: 0.5rem;
  white-space: pre;
}

.namedocs > .text .constructor .name-and-type {
  padding-left: 0.5rem;
  float: left;
  margin-top: 0;
}
.namedocs > .text .constructor .docs {
  clear: both;
  padding-left: 1rem;
}


.namedocs .methods td, .namedocs .fields td {
  vertical-align: top;
}
.namedocs .inheritance {
  vertical-align: top;
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
}
.namedocs .inheritance ol {
  display: inline-block;
  margin: 0;
  padding: 0;
}
.namedocs .inheritance ol li {
  list-style-type: none;
  display: inline-block;
}
.namedocs .inheritance ol li::after {
  content: " > "
}
.namedocs .inheritance ol li:last-child::after {
  content: "";
}

.namedocs .extends {
  display: inline;
  margin: 0;
  padding: 0;
}

.namedocs .extends li {
  list-style-type: none;
  display: inline-block;
}

.namedocs .extends li label {
  padding-right: 1rem;
}

.namedocs .subdocs .name-and-type {
  font-size: 1rem;
  margin-left: 0;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs .subdocs .docs {
  margin-left: 1.5rem;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs:has(input[data-parent-idx]) [data-inherited-from] {
  transition-property: opacity, display;
  transition-duration: 0.4s;
  transition-behavior: allow-discrete;
  @starting-style { opacity: 0 !important; }
}
"# ++ Id.run do
  let mut str := ""
  for i in [0:50] do
    str := str ++ mkFilterRule i
  str
where
  mkFilterRule (i : Nat) : String :=
    ".namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]) [data-inherited-from=\"" ++ toString i ++ "\"] {
  display: none;
  opacity: 0;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked) [data-inherited-from=\"" ++ toString i ++"\"] {
  display: table-row;
  transform: none;
  opacity: 1;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked):has(.inheritance[data-inherited-from=\"" ++ toString i ++"\"]:hover) [data-inherited-from]:not([data-inherited-from=\"" ++ toString i ++"\"]) {
  opacity: 0.5;
}
"


open Verso.Genre.Manual.Markdown in
@[block_extension Block.declaration]
def declaration.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle docstringDomain "Lean constant reference"
    |>.setDomainDescription docstringDomain "Documentation for Lean constants"

  traverse id info _ := do
    let .ok (name, declType, declInfo, _signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Block.DeclarationInfo × Option Highlighted) info
      | do logError "Failed to deserialize docstring data"; pure none

    match declType with
    | .structure true ctor fields fieldInfos _parents _ancestors =>
        saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Instance constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (class method)"])
            (showName := some f.toString)
    | .structure false ctor fields fieldInfos _parents _ancestors =>
        saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (structure field)"])
            (showName := some f.toString)
    | .inductive ctors _ _ =>
      for c in ctors do
        saveRef id c.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]
    | _ => pure ()

    -- Save a backreference
    match (← get).get? `Verso.Genre.Manual.docstring with
    | some (.error e) => logError e
    | some (.ok (v : Json)) =>
      let found : HashSet InternalId := (v.getObjVal? name.toString).bind fromJson? |>.toOption |>.getD {}
      modify (·.set `Verso.Genre.Manual.docstring <|  v.setObjVal! name.toString (toJson (found.insert id)))
    | none =>
      modify (·.set `Verso.Genre.Manual.docstring <| Json.mkObj [] |>.setObjVal! name.toString (toJson [id]))

    -- Save a new-style backreference
    modify fun st => st.saveDomainObject docstringDomain name.toString id
    saveRef id name none
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, declType, declInfo, signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Block.DeclarationInfo × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML"; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html ← Option.map Highlighted.toHtml signature |>.getD (pure {{ {{x}} }})

      let xref ← state
      let idAttr := xref.htmlId id
      let declarationName : String :=
        match declInfo.isDef, declInfo.isThm with
        | true, _ => "Definition"
        | false, true => "Theorem"
        | false, false => "Lemma"
      return {{
        <div style=" padding: 10px; border-radius: 4px;">
        <b>{{declarationName}}</b>{{ " (" ++ name.toString ++ ")" }}<b>{{":"}}</b>
        <div style="display: flex; justify-content: space-between; align-items: flex-start; margin-bottom: 10px;">
        <div style="margin-left: 1em; flex: 1;">{{← contents.mapM goB}}</div>
        </div>

        <div>
        <details class="code-block-container">
        <summary style="font-size: 0.8em; margin-left: 1em;">{{"Show Lean signature:"}}</summary>
          <pre class="signature hl lean block" style="background: none; margin: 0;">{{ sig }}</pre>
        </details>
        </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [declarationStyle]
}
where
  saveRef
      (id : InternalId) (name : Name)
      (subterm : Option (Doc.Inline Manual))
      (showName : Option String := none) :
      ReaderT TraverseContext (StateT TraverseState IO) Unit := do
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {
      term := Doc.Inline.code (showName.getD name.toString),
      subterm := subterm
    }
    modify (·.saveDomainObject docstringDomain name.toString id)

end Verso.Genre.Manual
