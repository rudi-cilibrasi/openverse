/-
  OpenVerse front end — attributes (Book of Verse ch. 12, "Annotations and
  Metadata"; the rules are pinned in docs/research/attributes.md).

  The parser keeps an attribute `@a`, `@a{F := e}` or `@a(…)` written before
  a definition among the specifiers of its name, as `@a`, and as a record
  after the definition, `$attr:L_C` (`attrTop`), whose specifiers are the
  definition's place, name and position and whose value is the attribute as
  written; an attribute on an expression is a form refused
  (`Refused.exprAttribute`), but `@ignore_unreachable`, which is nothing
  there, and is kept for a `case`'s arms (`TyEnv.ignoredArms`). `apply`
  refuses the forms the parser marked refused (`Refused`), checks every
  attribute and takes them out, before anything else reads the program:

  - the attribute exists: one of the Book's (`@deprecated`, `@experimental`,
    `@available`, `@attribscope_…`), or a class below `attribute` (a custom
    attribute), or a constructor function of one;
  - it may be written where it is: the Book's at the places its prose lists,
    a custom one where the scopes `@attribscope_…` of its class allow;
  - its arguments construct it: the Book's fields by their rules, a custom
    one's value `$attrCheck:N` of its class, which the elaborator checks and
    drops, as it does a function type's default (`checkTypeDefaults`), in
    the scope around the definition, which cannot see a class's members;
  - an attribute class and its constructors are named in attributes only
    (and in the attribute classes and constructors themselves).

  Then `@available{MinUploadedAtFNVersion := N}` takes a definition out of
  the program when `N` is a version openverse's programs are not at
  (`versionedOut`); everything else is metadata, with no effect on what the
  program does.
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front

/-- The last part of a qualified or dotted name: `c` of `A::B::c` or `M.c`. -/
def lastPartOf (n : String) : String :=
  let n := ((n.splitOn "::").getLast?.getD n)
  (n.splitOn ".").getLast?.getD n

/-- The names an expression writes that may name a definition: its
    identifiers, the types and classes it constructs, the types of its
    declarations and of the types it defines (not the members it reads
    through a value, which are no definitions' names). -/
partial def SExpr.namesWritten : SExpr → List String
  | .ident _ n => [n]
  | .construct _ n ts es => n :: ts.flatMap STy.allNames ++ es.flatMap SExpr.namesWritten
  | .decl _ _ ty _ x => (ty.map STy.allNames).getD [] ++ x.namesWritten
  | .structDef _ _ _ fs => fs.flatMap fun f => f.ty.allNames ++ (f.default.map SExpr.namesWritten).getD []
  | .typeAlias _ _ ty => ty.allNames
  | .refineDef _ _ base cs => base.allNames ++ cs.flatMap SExpr.namesWritten
  | e => e.children.flatMap SExpr.namesWritten

/-- The names a definition writes (`SExpr.namesWritten`), in its signature,
    its parents, its fields and its code. -/
partial def STop.namesWritten : STop → List String
  | .fn _ _ ps _ _ ret body =>
    ps.flatMap (fun p => p.ty.allNames ++ (p.default.map SExpr.namesWritten).getD []) ++ ret.allNames ++
      body.namesWritten
  | .const _ _ _ ty v => (ty.map STy.allNames).getD [] ++ v.namesWritten
  | .classDef _ _ _ _ _ parents _ fs ms =>
    parents.flatMap STy.allNames ++ fs.flatMap (fun f => f.ty.allNames ++ (f.default.map SExpr.namesWritten).getD []) ++
      ms.flatMap STop.namesWritten

/-- The first form in `e` that openverse parses and refuses (`Refused`,
    `refusedForm`), with the message that refuses it. -/
partial def SExpr.refusal? : SExpr → Option (Pos × String)
  | .structDef _ _ _ fs => fs.findSome? fun f => f.default.bind SExpr.refusal?
  | .refineDef _ _ _ cs => cs.findSome? SExpr.refusal?
  | e => e.refused? <|> e.children.findSome? SExpr.refusal?

partial def STop.refusal? : STop → Option (Pos × String)
  | .fn _ _ ps _ _ _ body => (ps.findSome? fun p => p.default.bind SExpr.refusal?) <|> body.refusal?
  | .const _ _ _ _ v => v.refusal?
  | .classDef _ _ _ _ _ _ _ fs ms => (fs.findSome? fun f => f.default.bind SExpr.refusal?) <|> ms.findSome? STop.refusal?

/-- A definition without the attributes among its specifiers (`@a`). -/
def STop.withoutAttrSpecs : STop → STop
  | .fn p n ps tps specs r b =>
    .fn p n ps tps (specs.filter (!·.startsWith "@")) r (dropFieldSpecs b)
  | .const p n specs t v => .const p n (specs.filter (!·.startsWith "@")) t (dropFieldSpecs v)
  | .classDef p n ns tps specs ps i fs ms =>
    .classDef p n (ns.filter (!·.startsWith "@")) tps specs ps i (fs.map fun f => { f with specs := f.specs.filter (!·.startsWith "@") })
      (ms.map fun
        | .fn mp mn mps mtps mspecs mr mb => .fn mp mn mps mtps (mspecs.filter (!·.startsWith "@")) mr mb
        | m => m)
where
  dropFieldSpecs : SExpr → SExpr
    | .structDef p tps specs fs => .structDef p tps specs (fs.map fun f => { f with specs := f.specs.filter (!·.startsWith "@") })
    | e => e

/-- The names an expression writes that may name a definition, each where
    it is (`SExpr.namesWritten`), with the dotted names of chains of names
    (`enum1.A`, `M.F`). -/
partial def SExpr.namesAt : SExpr → List (Pos × String)
  | .ident p n => [(p, n)]
  | .member p x m =>
    let rec dotted : SExpr → Option String
      | .ident _ n => some n
      | .member _ y k => (dotted y).map (· ++ "." ++ k)
      | _ => none
    ((dotted x).map (fun d => [(p, d ++ "." ++ m)])).getD [] ++ x.namesAt
  | .construct p n ts es => (p, n) :: ts.flatMap (fun t => t.allNames.map (p, ·)) ++ es.flatMap SExpr.namesAt
  | .decl p _ ty _ x => ((ty.map STy.allNames).getD []).map (p, ·) ++ x.namesAt
  | .structDef p _ _ fs => fs.flatMap fun f => f.ty.allNames.map (p, ·) ++ (f.default.map SExpr.namesAt).getD []
  | .typeAlias p _ ty => ty.allNames.map (p, ·)
  | .refineDef p _ base cs => base.allNames.map (p, ·) ++ cs.flatMap SExpr.namesAt
  | e => e.children.flatMap SExpr.namesAt

namespace Attributes

/-- An attribute as the parser recorded it (`attrTop`). -/
structure Use where
  pos : Pos
  /-- The scope of the definition it is on: `A::B::` in a module. -/
  pfx : String
  /-- What the definition is (`STop.attrPlace`, or a member's place), with
      `:override` for an override. -/
  place : String
  /-- The definition's name, `c.M` for a member. -/
  target : String
  /-- The attribute as written. -/
  expr : SExpr
  /-- Where the definition it is on is in the program as parsed (for a
      member, its class). -/
  defIdx : Nat := 0
  deriving Inhabited

def Use.head (u : Use) : String := u.expr.attrHead

/-- The place without its `:override`. -/
def Use.base (u : Use) : String := (u.place.splitOn ":").headD u.place

/-- What a place is, for messages. -/
def placeWhat : String → String
  | "function" => "a function"
  | "method" => "a method"
  | "field" => "a class's or an interface's field"
  | "structField" => "a struct's field"
  | "enumerator" => "an enum's value"
  | "class" => "a class"
  | "attribclass" => "an attribute class"
  | "interface" => "an interface"
  | "struct" => "a struct"
  | "enum" => "an enum"
  | "alias" => "a type alias"
  | "data" => "a constant"
  | "module" => "a module"
  | "constructor" => "a constructor function"
  | "scope" => "an access scope"
  | p => p

/-- The scopes `@attribscope_X` an attribute class may have, each with the
    places it admits (Book of Verse ch. 12, "Attribute Scopes", and its
    tests, `CustomAttributes.versetest`, `Enum.versetest`, `Function.versetest`:
    `attribscope_enumerator` and `attribscope_name`, the latter a place
    openverse has none of, a name's specifier `<attr>`). -/
def scopes : List (String × List String) :=
  [("attribscope_class", ["class", "attribclass"]),
   ("attribscope_attribclass", ["attribclass"]),
   ("attribscope_enum", ["enum"]),
   ("attribscope_enumerator", ["enumerator"]),
   ("attribscope_interface", ["interface"]),
   ("attribscope_function", ["function", "method"]),
   ("attribscope_data", ["data", "field", "structField"]),
   ("attribscope_name", [])]

/-- Where `@deprecated`, `@experimental` and `@available` may be written (ch.
    12: "Functions and methods; Classes, interfaces, structs, and enums;
    Individual enum values; Data members; Modules"; `@available` "the same
    kinds of definitions as `@deprecated`"; type aliases, its tests,
    `deprecated.versetest:435`). -/
def metadataPlaces : List String :=
  ["function", "method", "class", "attribclass", "interface", "struct", "enum", "enumerator", "data", "field",
   "structField", "module", "alias"]

/-- The largest version number, which no upload reaches: a definition
    `@available{MinUploadedAtFNVersion := N}` with `N` at least this is
    versioned out of every openverse program, any other is in (its tests:
    `available.versetest:304` versions `4294967295` out, `:326` versions
    `3000` in, `:6`-`:62` version `0` in). -/
def versionedOut : Int := 4294967295

def err (p : Pos) (msg : String) : Except String α := .error s!"{p.show}: {msg}"

def lastPart (n : String) : String := lastPartOf n

/-- The fields of a built-in attribute's `{…}`: each name with its value,
    none twice, each one the attribute has (`fields`). -/
def builtinFields (u : Use) (fs : List SExpr) (fields : List String) : Except String (List (String × SExpr)) := do
  let mut out : List (String × SExpr) := []
  for f in fs do
    match f with
    | .decl _ n none false v =>
      if !fields.contains n then
        err u.pos s!"@{u.head} has no field {n}: its fields are {", ".intercalate fields} (Book of Verse ch. 12)"
      if out.any (·.1 == n) then err u.pos s!"@{u.head} gives {n} twice"
      out := out ++ [(n, v)]
    | _ => err u.pos s!"@{u.head}\{…} gives its fields as Name := value"
  return out

/-- Whether an expression is the literal `false`. -/
def isFalse : SExpr → Bool
  | .ident _ "false" => true
  | _ => false

/-- The warnings of uses of deprecated definitions (Book of Verse ch. 12,
    "@deprecated": "When code references a deprecated definition, the
    compiler produces a warning"; "Deprecated definitions can use other
    deprecated definitions without warnings"), each at the use: a name of a
    deprecated definition, of a member of a deprecated module or of a value
    of a deprecated enum, written in a definition that is not deprecated
    itself; and an override of a deprecated member that is not deprecated
    (its tests, deprecated.versetest 488, 512). A name that is also an
    overload that is not deprecated is not judged: which one it names is the
    elaboration's to decide. -/
def deprecations (tops : List STop) (uses : List Use) : List (Pos × String) := Id.run do
  let deps := uses.filter (·.head == "deprecated")
  let memberPlaces := ["method", "field", "structField", "enumerator"]
  let defs : List String := (deps.filter (!memberPlaces.contains ·.base)).map (·.target)
  let modules : List String := (deps.filter (·.place == "module")).map (·.target)
  let members : List String := (deps.filter (memberPlaces.contains ·.base)).map (·.target)
  -- (a deprecated enum's values are deprecated with it)
  let enumValues : List String := tops.flatMap fun
    | .const _ n _ _ (.enumDef _ vs _) => if defs.contains n then vs.map (n ++ "." ++ ·) else []
    | _ => []
  let inModule (n : String) : Bool := modules.any fun m => n.startsWith (m ++ "::")
  let isDeprecated (n : String) : Bool := defs.contains n || inModule n
  let names : List String := tops.filterMap fun
    | .fn _ n .. | .classDef _ n .. => some n
    | .const _ n .. => if n.startsWith "$" then none else some n
  -- (what a written name `x`, `M.x` or `(q:)x` names, by its parts: a
  -- definition of that last name whose module path ends with the rest)
  let writes (written d : String) : Bool :=
    let w := (((bareName written).splitOn ".")).filter (· != "")
    let parts := d.splitOn "::"
    w.length ≤ parts.length && parts.drop (parts.length - w.length) == w
  let named (written : String) : Option String :=
    let cands := names.filter (writes written ·)
    if cands.isEmpty || !cands.all isDeprecated then none else cands.head?
  let memberNamed (written : String) : Option String :=
    (members ++ enumValues).find? fun m =>
      let i := (m.splitOn ".")
      let w := written.splitOn "."
      w.length ≥ 2 && i.length ≥ 2 && i.getLast? == w.getLast? &&
        writes (".".intercalate w.dropLast) (".".intercalate i.dropLast) &&
        (names.any (fun n => n == ".".intercalate i.dropLast))
  let mut out : Array (Pos × String) := #[]
  for t in tops do
    let (p, n) := match t with | .fn p n .. | .const p n .. | .classDef p n .. => (p, n)
    if n.startsWith "$" || isDeprecated n then continue
    let written : List (Pos × String) := match t with
      | .fn p _ ps _ _ ret body =>
        ps.flatMap (fun q => q.ty.allNames.map (p, ·) ++ (q.default.map SExpr.namesAt).getD []) ++
          ret.allNames.map (p, ·) ++ body.namesAt
      | .const p _ _ ty v => ((ty.map STy.allNames).getD []).map (p, ·) ++ v.namesAt
      | .classDef p _ _ _ _ parents _ fs ms =>
        parents.flatMap (fun t => t.allNames.map (p, ·)) ++
          fs.flatMap (fun f => (if members.contains s!"{n}.{f.name}" then [] else
            f.ty.allNames.map (p, ·) ++ (f.default.map SExpr.namesAt).getD [])) ++
          ms.flatMap fun
            | .fn mp mn ps _ _ ret body =>
              if members.contains s!"{n}.{mn}" then [] else
              ps.flatMap (fun q => q.ty.allNames.map (mp, ·) ++ (q.default.map SExpr.namesAt).getD []) ++
                ret.allNames.map (mp, ·) ++ body.namesAt
            | _ => []
    for (q, w) in written do
      if let some d := named w then
        out := out.push (q, s!"{(d.splitOn "::").getLast?.getD d} is deprecated{message d}")
      else if let some m := memberNamed w then
        out := out.push (q, s!"{m} is deprecated{message m}")
    -- (an override of a deprecated member, itself not deprecated)
    if let .classDef p _ _ _ _ _ _ fs ms := t then
      let over : List (Pos × String) := fs.filterMap (fun f =>
          if f.isOverride && !members.contains s!"{n}.{f.name}" then some (p, f.name) else none) ++
        ms.filterMap fun
          | .fn mp mn _ _ specs .. =>
            if specs.contains "override" && !members.contains s!"{n}.{mn}" then some (mp, mn) else none
          | _ => none
      for (q, m) in over do
        if let some d := members.find? (fun d => (d.splitOn ".").getLast? == some m && !d.startsWith (n ++ ".")) then
          out := out.push (q, s!"{n}.{m} overrides {d}, which is deprecated{message d}")
  return out.toList
where
  /-- The deprecation's message, if it has one. -/
  message (d : String) : String :=
    match ((uses.find? fun u => u.head == "deprecated" && u.target == d).map (·.expr) : Option SExpr) with
    | some (SExpr.construct _ _ _ fs) =>
      match fs.findSome? (fun | .decl _ "Message" none false (.str _ [.text m]) => some m | _ => none) with
      | some m => s!": {m}"
      | none => ""
    | _ => ""

/-- The program with its attributes checked and taken out (the file's
    comment says what is checked), the values of custom attributes added as
    `$attrCheck:N` constants, and the definitions `@available` versions out
    removed. -/
def apply (tops : List STop) : Except String (List STop × List (Pos × String)) := do
  let isRecord : STop → Bool := fun
    | .const _ n .. => ((n.splitOn "::").getLast?.getD n).startsWith attrPrefix
    | _ => false
  if !tops.any isRecord && !tops.any (·.refusal?.isSome) && !tops.any (·.namesWritten.contains pointerTypeHead) then
    return (tops, [])
  let tops0 := tops.toArray
  -- the records, in order, each with the definition before it
  let uses : List Use := tops.zipIdx.filterMap fun
    | (.const p n (place :: target :: _) none e, i) =>
      let last := (n.splitOn "::").getLast?.getD n
      if !last.startsWith attrPrefix then none else
      let defIdx := ((List.range i).reverse.find? fun j => !tops0[j]!.isBesideMarker).getD 0
      some { pos := p, pfx := (n.dropEnd last.length).toString, place, target, expr := e, defIdx }
    | _ => none
  -- `@available` versions a definition out (`versionedOut`): it and, for a
  -- module, its members are taken out of the program
  let gone : List Use := uses.filter fun u =>
    u.head == "available" && match u.expr with
      | .construct _ _ _ fs => fs.any fun
        | .decl _ "MinUploadedAtFNVersion" none false (.int _ v) => v ≥ versionedOut
        | _ => false
      | _ => false
  let memberPlaces := ["method", "field", "structField", "enumerator"]
  let goneIdx : List Nat := (gone.filter (!memberPlaces.contains ·.base)).map (·.defIdx)
  let goneModules : List String := (gone.filter (·.place == "module")).map (·.target)
  let inGoneModule (n : String) : Bool := goneModules.any fun m =>
    let n := (moduleMarker? n).getD n
    let n := (afterPrefix? qualPrefix n <|> afterPrefix? openPrefix n).getD n
    n.startsWith (m ++ "::")
  -- (a member: by its name, a method the first of its name after the attribute)
  let posLe (a b : Pos) : Bool := a.line < b.line || (a.line == b.line && a.col ≤ b.col)
  let goneMember (owner m : String) : Bool := gone.any fun u =>
    memberPlaces.contains u.base && u.target == s!"{owner}.{m}"
  let tops := tops.zipIdx.filterMap fun (t, i) =>
    let n := match t with | .fn _ n .. | .const _ n .. | .classDef _ n .. => n
    if goneIdx.contains i || inGoneModule n then none else some <| match t with
      | .const p n specs ty (.enumDef q vs o) => .const p n specs ty (.enumDef q (vs.filter (!goneMember n ·)) o)
      | .const p n specs ty (.structDef q tps ss fs) =>
        .const p n specs ty (.structDef q tps ss (fs.filter (!goneMember n ·.name)))
      | .classDef p n ns tps specs ps isI fs ms =>
        let goneMethods : List Pos := gone.filterMap fun u =>
          if u.base != "method" || !u.target.startsWith (n ++ ".") then none else
          let mn := (u.target.drop (n.length + 1)).toString
          (ms.filterMap (fun | .fn mp m .. => if m == mn && posLe u.pos mp then some mp else none | _ => none)).head?
        .classDef p n ns tps specs ps isI (fs.filter (!goneMember n ·.name))
          (ms.filter fun | .fn mp .. => !goneMethods.contains mp | _ => true)
      | t => t
  let tops := (tops.filter (!isRecord ·)).map STop.withoutAttrSpecs
  -- (an attribute on an expression or a local definition: Book of Verse
  -- tests, deprecated.versetest:83, experimental.versetest:35, 3604, 3553)
  if let some (p, msg) := tops.findSome? STop.refusal? then err p msg
  -- (a pointer type, `^t`)
  if let some t := tops.find? (·.namesWritten.contains pointerTypeHead) then
    let p := match t with | .fn p .. | .const p .. | .classDef p .. => p
    err p Refused.pointerType.message
  -- the attribute classes: the classes below `attribute`, by name
  let classes : List (String × List STy) := tops.filterMap fun
    | .classDef _ n _ _ _ ps false .. => some (n, ps)
    | _ => none
  let definesAttribute := tops.any fun
    | .classDef _ n .. | .const _ n .. | .fn _ n .. => lastPart n == "attribute"
  let parentName : STy → String := fun
    | .name n | .app n _ => lastPart n
    | _ => ""
  let mut attrClasses : List String := []
  for _ in [0:classes.length + 1] do
    let next := classes.filterMap fun (n, ps) =>
      if ps.any (fun t => let q := parentName t
          (q == "attribute" && !definesAttribute) || attrClasses.any (lastPart · == q)) then some n else none
    if next.length == attrClasses.length then break
    attrClasses := next
  let isAttrClass (n : String) : Bool := attrClasses.any (lastPart · == lastPart n)
  -- (the constructor functions of attribute classes, `c<constructor>(…) := a{…}`)
  let ctors : List (String × String) := tops.filterMap fun
    | .fn _ n _ _ specs .. =>
      match specs.findSome? constructorSpec? with
      | some c => if isAttrClass c then some (n, c) else none
      | none => none
    | _ => none
  let ctorOf? (n : String) : Option String := (ctors.find? (lastPart ·.1 == lastPart n)).map (·.2)
  -- (each use's place: a class below `attribute` is an attribute class)
  let uses := uses.map fun u =>
    if u.place == "class" && isAttrClass u.target then { u with place := "attribclass" } else u
  -- each attribute class's scopes, from its own `@attribscope_…`
  let scopesOf (c : String) : List String := uses.filterMap fun u =>
    if u.place == "attribclass" && lastPart u.target == lastPart c && (scopes.lookup u.head).isSome then
      some u.head else none
  -- check each attribute, and write the values of custom ones
  let mut checks : Array STop := #[]
  for u in uses do
    let h := u.head
    let isBuiltin := ["deprecated", "experimental", "available", "ignore_unreachable"].contains h ||
      (scopes.lookup h).isSome
    if u.target.endsWith ".$block" then
      err u.pos s!"@{h} is on block:, which is no definition"
    if isBuiltin then
      if let some _ := scopes.lookup h then
        match u.expr with
        | .ident .. => pure ()
        | _ => err u.pos s!"@{h} takes no arguments"
        if u.place != "attribclass" then
          err u.pos s!"@{h} is not allowed on {placeWhat u.base}: it gives an attribute class (a class below attribute) the places it may be written at (Book of Verse ch. 12, \"Attribute Scopes\")"
      else if h == "ignore_unreachable" then
        err u.pos "@ignore_unreachable goes on an expression or a case arm, whose code it lets be one never reached, not on a definition"
      else
        if !metadataPlaces.contains u.base then
          err u.pos s!"@{h} is not allowed on {placeWhat u.base} (Book of Verse ch. 12: functions and methods, classes, interfaces, structs, enums and their values, data members, modules)"
        if h == "experimental" && u.place.endsWith ":override" then
          err u.pos "@experimental is not allowed on an override: it is experimental when what it overrides is (Book of Verse ch. 12)"
        let fieldsOf : List String := match h with
          | "deprecated" => ["Message", "DiscontinuedAtFNVersion"]
          | "available" => ["MinUploadedAtFNVersion"]
          | _ => []
        let given ← match u.expr with
          | .ident .. => pure []
          | .construct _ _ [] fs =>
            if h == "experimental" && !fs.isEmpty then err u.pos "@experimental has no fields"
            else builtinFields u fs fieldsOf
          | _ => err u.pos s!"@{h}(…) is not an attribute: write @{h}{if fieldsOf.isEmpty then "" else " or @" ++ h ++ "{" ++ fieldsOf.headD "" ++ " := …}"} (Book of Verse ch. 12; its tests, deprecated.versetest:128)"
        for (n, v) in given do
          let ty : STy := if n == "Message" then .name "string" else .name "int"
          -- (`Message := false` is no message, ch. 12)
          if n == "Message" && isFalse v then continue
          checks := checks.push (.const u.pos s!"{u.pfx}{attrCheckPrefix}{checks.size}@{h}" [] (some ty) v)
        if h == "deprecated" && (given.lookup "DiscontinuedAtFNVersion").isSome then
          match given.lookup "Message" with
          | none => err u.pos "@deprecated with DiscontinuedAtFNVersion needs a Message, which is not empty (Book of Verse tests, deprecated.versetest:160)"
          | some m =>
            if isFalse m || m == .str m.pos [] then
              err u.pos "@deprecated with DiscontinuedAtFNVersion needs a Message, which is not empty (Book of Verse tests, deprecated.versetest:166)"
        if h == "available" then
          match given.lookup "MinUploadedAtFNVersion" with
          | some (.int _ _) | none => pure ()
          | some _ => err u.pos "openverse reads @available's MinUploadedAtFNVersion as an integer literal"
      continue
    -- a custom attribute: a class below `attribute`, or a constructor of one
    if let .app _ (.ident _ c) _ _ := u.expr then
      if c == attrCallHead then
        err u.pos s!"@{h}(…)\{…}: an attribute is a class's value, constructed with \{…}, or a constructor's call (…), not both"
    let (cls, value) ← match u.expr with
      | .app p f args false =>
        match ctorOf? h with
        | some c => pure (c, SExpr.app p f args false)
        | none =>
          if isAttrClass h then
            err u.pos s!"@{h}(…): an attribute class is constructed with \{…}, not called (Book of Verse tests, deprecated.versetest:128)"
          else err u.pos s!"@{h} names no attribute: an attribute is @deprecated, @experimental, @available, @attribscope_…, a class below attribute, or a constructor function of one (Book of Verse ch. 12)"
      | e@(.construct ..) =>
        if isAttrClass h then pure (h, e)
        else err u.pos s!"@{h} names no attribute: an attribute is @deprecated, @experimental, @available, @attribscope_…, a class below attribute, or a constructor function of one (Book of Verse ch. 12)"
      | .ident p _ | .member p .. =>
        if isAttrClass h then pure (h, SExpr.construct p h [] [])
        else if let some c := ctorOf? h then
          err u.pos s!"@{h}: {h} is a constructor of the attribute class {lastPart c}, called with its arguments, @{h}(…)"
        else err u.pos s!"@{h} names no attribute: an attribute is @deprecated, @experimental, @available, @attribscope_…, a class below attribute, or a constructor function of one (Book of Verse ch. 12)"
      | _ => err u.pos s!"@{h} names no attribute"
    let allowed := (scopesOf cls).flatMap fun sc => (scopes.lookup sc).getD []
    if !allowed.contains u.base then
      let scs := scopesOf cls
      err u.pos s!"@{h} is not allowed on {placeWhat u.base}: the attribute class {lastPart cls} has {if scs.isEmpty then "no scope" else "the scopes " ++ ", ".intercalate (scs.map ("@" ++ ·))} (Book of Verse ch. 12, \"Attribute Scopes\")"
    checks := checks.push (.const u.pos s!"{u.pfx}{attrCheckPrefix}{checks.size}@{h}" [] (some (.name cls)) value)
  -- an attribute class and its constructors are named in attributes only
  -- (Book of Verse tests, SOL-1729-MakeAttributesForwardCompatible: 3670)
  let special : List String := attrClasses.map lastPart ++ ctors.map (lastPart ·.1)
  if !special.isEmpty then
    for t in tops do
      let own := match t with
        | .classDef _ n .. => isAttrClass n
        | .fn _ n .. => (ctorOf? n).isSome
        | _ => false
      if own then continue
      if let some n := t.namesWritten.find? (special.contains ·) then
        let p := match t with | .fn p .. | .const p .. | .classDef p .. => p
        err p s!"{n} is {if attrClasses.any (lastPart · == n) then "an attribute class" else "a constructor of an attribute class"}: it is named in attributes only, @{n} (Book of Verse tests, SOL-1729-MakeAttributesForwardCompatible)"
  -- the class `attribute` (Book of Verse ch. 12, "Custom Attributes"), when
  -- the program's classes are below it
  let pre : List STop := if attrClasses.isEmpty || definesAttribute then [] else
    let p : Pos := { line := 0, col := 0 }
    [.classDef p "attribute" [] [] ["abstract", "computes"] [] false [] []]
  return (pre ++ tops ++ checks.toList, deprecations tops uses)

end Attributes
end OpenVerse.Front
