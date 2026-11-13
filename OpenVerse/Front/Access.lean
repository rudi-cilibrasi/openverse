/-
  OpenVerse front end — access specifiers (Book of Verse ch. 12; the rules
  are pinned in docs/research/access-specifiers.md).

  One order. A specifier written on a definition denotes the code that may
  use it, its audience (`Audience`): everyone (`<public>`), Epic's code
  (`<epic_internal>`; openverse's program stands where the Book's test
  snippets do, in an Epic-internal scope, so all of it), a module and what is
  inside it (`<internal>`), a class and the classes below it (`<protected>`),
  a class (`<private>`). A definition's effective audience (`Eff`) is the
  intersection of its own and those of the definitions it is in: its class,
  its modules. "At least as visible as" is containment of audiences
  (`Audience.within`). Two kinds of rule use it:

  - access: a use is admitted where every audience of what it names admits
    the code it is written in (`Eff.admits`): a module's members are checked
    where the modules' renaming resolves them (`Front/Modules.lean`); a
    construction's class, the fields it gives, a class's parents and what an
    override overrides by `checkUses` on the resolved program; a member
    reached through a value by the elaborator, which alone knows the value's
    class (`Env.member?`), at the code found by position (`Sites`);
  - consistency: a definition exposes nothing less visible than itself
    (`checkConsistency`).

  Nothing here changes what is generated.
-/
import OpenVerse.Front.EffectPolicy
import Std.Data.HashMap

namespace OpenVerse.Front.Access

/-- Where code is: its module (the top level is `[]`) and, in a class's or an
    interface's code (a method, a field's default, a `block:`), the class. -/
structure Site where
  module : List String
  cls : Option String := none
  deriving BEq, Repr, Inhabited

/-- The code an access specifier admits. -/
inductive Audience where
  /-- `<public>`: any code. -/
  | everyone
  /-- `<epic_internal>`: Epic's code, which a program is (the Book's tests'
      scope); not other packages'. -/
  | epic
  /-- `<internal>`: code in the module or a module inside it. -/
  | within (m : List String)
  /-- `<scoped{G, …}>`: code in the module, or in one of the granted ones, or
      inside them. -/
  | scoped (m : List String) (grants : List (List String))
  /-- `<protected>`: code of the class or of a class below it, in any module. -/
  | below (c : String)
  /-- `<private>`: code of the class itself. -/
  | inClass (c : String)
  deriving BEq, Repr, Inhabited

/-- An effective audience: the intersection of a definition's own audience and
    those of the definitions it is in. -/
abbrev Eff := List Audience

/-- The access level written in `specs`, if any. -/
def levelOf (specs : List String) : Option String := specs.find? EffectPolicy.isAccess

/-- An access level `scoped{A::B|C}` as `resolveSpecifiers` writes it: the
    modules it grants, by their parts. -/
def scopedGrants? (sp : String) : Option (List (List String)) :=
  if sp.startsWith "scoped{" && sp.endsWith "}" then
    let inner := ((sp.drop "scoped{".length).dropEnd 1).toString
    some ((inner.splitOn "|").filter (· != "") |>.map (·.splitOn "::"))
  else none

/-- The access level `scoped{…}` that grants the modules `gs`. -/
def scopedLevel (gs : List (List String)) : String :=
  "scoped{" ++ "|".intercalate (gs.map ("::".intercalate ·)) ++ "}"

/-- The audience of access `sp` (the default, `<internal>`, when none) on a
    definition of module `m`, and of class `c` for a class's member or
    constructor. -/
def audience (sp : Option String) (m : List String) (c : Option String := none) : Audience :=
  match sp, c with
  | some "public", _ => .everyone
  | some "epic_internal", _ => .epic
  | some "protected", some c => .below c
  | some "private", some c => .inClass c
  | some s, _ => match scopedGrants? s with
    | some gs => .scoped m gs
    | none => .within m
  | _, _ => .within m


def isPrefix (a b : List String) : Bool := a.length ≤ b.length && b.take a.length == a

/-- Whether code at `s` is in the audience (`below c d`: class `c` is `d` or
    below it). -/
def Audience.admits (below : String → String → Bool) (s : Site) : Audience → Bool
  | .everyone | .epic => true
  | .within m => isPrefix m s.module
  | .scoped m gs => isPrefix m s.module || gs.any (isPrefix · s.module)
  | .below c => s.cls.any (below · c)
  | .inClass c => s.cls == some c

def Eff.admits (below : String → String → Bool) (s : Site) (e : Eff) : Bool := e.all (·.admits below s)

/-- The first audience of `e` that does not allow code at `s`. -/
def Eff.denial (below : String → String → Bool) (s : Site) (e : Eff) : Option Audience :=
  e.find? (!·.admits below s)

/-- `a ⊆ b`: all the code `a` admits, `b` admits (the visibility order: `b`
    is at least as visible as `a`). A class's code is in its module
    (`moduleOf`); a program's code is Epic's. A class's subclasses may be in
    any module, of any package, where the class is visible: `below c` is in
    no module's audience by itself (the effective audience of a member of `c`
    also has `c`'s). -/
def Audience.inside (below : String → String → Bool) (moduleOf : String → List String) :
    Audience → Audience → Bool
  | _, .everyone => true
  | .everyone, _ => false
  | .epic, b => b == .epic
  | .below c, b => match b with
    | .below d => below c d
    | _ => false
  | .inClass c, b => match b with
    | .inClass d => c == d
    | .below d => below c d
    | b => moduleInside (moduleOf c) b
  | .within m, b => moduleInside m b
  | .scoped m gs, b => moduleInside m b && gs.all (moduleInside · b)
where
  /-- Code in module `m` (or inside it) is all in `b`. -/
  moduleInside (m : List String) : Audience → Bool
    | .everyone | .epic => true
    | .within n => isPrefix n m
    | .scoped n hs => isPrefix n m || hs.any (isPrefix · m)
    | _ => false

/-- `e ⊆ f`, an effective audience in another: each audience of `f` contains
    one of `e`'s. -/
def Eff.inside (below : String → String → Bool) (moduleOf : String → List String) (e f : Eff) : Bool :=
  f.all fun b => e.any (·.inside below moduleOf b)

/-- A module or class as messages show it: `A.B`, the top level. -/
def shown (n : String) : String := ".".intercalate (n.splitOn "::")

def shownModule (m : List String) : String := if m.isEmpty then "the top level" else ".".intercalate m

/-- What an audience is, for messages. -/
def Audience.what : Audience → String
  | .everyone => "<public>"
  | .epic => "<epic_internal>"
  | .within m => s!"internal to {shownModule m}"
  | .scoped m gs => s!"scoped to {", ".intercalate ((m :: gs).eraseDups.map shownModule)}"
  | .below c => s!"<protected> in {shown c}, for {shown c} and the classes below it"
  | .inClass c => s!"<private> to {shown c}"

/-- The module a definition `A::B::x` (or class) is in. -/
def moduleOfName (n : String) : List String := ((n.splitOn "::").dropLast)

/-- The levels written on a program's definitions and modules, by qualified
    name (`A::B::F`, a module's `A::B`); a name absent has none. -/
abbrev Levels := Std.HashMap String String

/-- The levels of the definitions of `tops` as parsed: functions, constants,
    types and aliases, classes, and modules (by their markers). -/
def Levels.of (tops : List STop) : Levels := tops.foldl (fun m t =>
  let (n, specs) : String × List String := match t with
    | .fn _ n _ _ specs .. | .const _ n specs .. | .classDef _ n specs .. => (n, specs)
  let n := if n.startsWith "$module:" then (n.drop "$module:".length).toString else n
  match levelOf specs with
  | some l => m.insert n l
  | none => m) {}

/-- The effective audience of a module, by its parts, as code inside other
    modules sees it: each level of it. -/
def Levels.module (lv : Levels) (path : List String) : Eff :=
  (List.range path.length).map fun k =>
    let lvl := path.take (k + 1)
    audience lv["::".intercalate lvl]? lvl.dropLast

/-- The effective audience of a definition of a module or the top level. -/
def Levels.definition (lv : Levels) (n : String) : Eff :=
  let m := moduleOfName n
  audience lv[n]? m :: lv.module m

/-- Where each piece of the source is: its definitions' positions, each with
    its site, by file; a position is in the last definition that starts at or
    before it. Made from the resolved source before any function is inlined or
    generated, so code later moved elsewhere is still judged where it is
    written. -/
structure Sites where
  byFile : Std.HashMap String (Array (Nat × Nat × Site)) := {}
  deriving Inhabited

def Sites.of (tops : List STop) : Sites := Id.run do
  let mut byFile : Std.HashMap String (Array (Nat × Nat × Site)) := {}
  let add (byFile : Std.HashMap String (Array (Nat × Nat × Site))) (p : Pos) (s : Site) :
      Std.HashMap String (Array (Nat × Nat × Site)) :=
    byFile.insert p.file ((byFile.getD p.file #[]).push (p.line, p.col, s))
  for t in tops do
    match t with
    | .fn p n .. | .const p n .. =>
      if !(((n.splitOn "::").getLastD n).startsWith "$") then
        byFile := add byFile p { module := moduleOfName n }
    | .classDef p n _ _ _ _ _ _ ms =>
      let s : Site := { module := moduleOfName n, cls := some n }
      byFile := add byFile p s
      for m in ms do
        if let .fn mp .. := m then byFile := add byFile mp s
  let lt (a b : Nat × Nat × Site) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  return { byFile := byFile.fold (fun acc f xs => acc.insert f (xs.qsort lt)) {} }

/-- The site of the code at `p`, if `p` is in the source. -/
def Sites.at (s : Sites) (p : Pos) : Option Site := do
  let xs ← s.byFile[p.file]?
  let mut best : Option Site := none
  for (l, c, site) in xs do
    if l < p.line || (l == p.line && c ≤ p.col) then best := some site else break
  best

/-- A member of a class or interface as it is declared there: the class, its
    effective audiences for reading and for writing (a field's `var<…>`), and
    whether it overrides. -/
structure Member where
  cls : String
  read : Eff
  write : Eff
  isOverride : Bool
  deriving Inhabited

/-- What the elaborator needs to judge a use of a class's member: the sites
    of the source, each class's members by `c.m`, each class's (and
    struct's) constructor audience, the classes' modules. -/
structure Env where
  sites : Sites := {}
  members : Std.HashMap String Member := {}
  ctors : Std.HashMap String Eff := {}
  classes : Std.HashMap String (List String) := {}
  deriving Inhabited

/-- A method's or field's source name: `M` for an overload `M$ovK`. -/
def sourceName (m : String) : String := (m.splitOn "$ov").headD m

/-- The class's effective audience. -/
def classEff (lv : Levels) (c : String) : Eff := lv.definition c

/-- The audience a class's (or struct's, interface's) own access specifier,
    `class<internal>`, gives its constructor, beside the class's: none when it
    writes none (Book of Verse tests, Classes/AccessSpecifiers 410-422). -/
def ctorEff (specs : List String) (m : List String) (c : String) : Eff :=
  match levelOf specs with
  | some l => [audience (some l) m (some c)]
  | none => []


/-- The access environment of a resolved program: each class's and
    interface's members, and each class's and struct's constructor (`lv`, the
    definitions' and modules' levels as parsed). -/
def Env.of (lv : Levels) (sites : Sites) (tops : List STop) : Env := Id.run do
  let mut env : Env := { sites }
  for t in tops do
    match t with
    | .classDef _ c _ _ specs _ _ fields methods =>
      let m := moduleOfName c
      let ce := classEff lv c
      env := { env with classes := env.classes.insert c m, ctors := env.ctors.insert c (ctorEff specs m c ++ ce) }
      for f in fields do
        let read := audience (levelOf f.specs) m (some c) :: ce
        let write := match levelOf f.varSpecs with
          | some w => audience (some w) m (some c) :: read
          | none => read
        let key := s!"{c}.{bareName f.name}"
        let member : Member := { cls := c, read, write, isOverride := f.isOverride }
        env := { env with members := env.members.insert key member }
      for meth in methods do
        if let .fn _ mn _ _ mspecs .. := meth then
          if mn.startsWith "$" then continue
          let key := s!"{c}.{bareName mn}"
          if env.members.contains key then continue
          let read := audience (levelOf mspecs) m (some c) :: ce
          let member : Member := { cls := c, read, write := read, isOverride := mspecs.contains "override" }
          env := { env with members := env.members.insert key member }
    | .const _ n _ _ (.structDef _ _ specs _) =>
      let m := moduleOfName n
      env := { env with ctors := env.ctors.insert n (ctorEff specs m n ++ lv.definition n) }
    | _ => pure ()
  return env

/-- The declaration of member `m` that a use through a value of a class whose
    classes and interfaces above are `supers` (itself first) reaches: the one
    that introduces it, whose access its overrides have (Book of Verse tests,
    AccessLevelInheritance), or the nearest. -/
def Env.member? (env : Env) (supers : List String) (m : String) : Option Member :=
  let ds := supers.filterMap fun c => env.members[s!"{c}.{sourceName (bareName m)}"]?
  (ds.find? (!·.isOverride)).orElse fun _ => ds.head?

/-- Why code may not use `what`, which audience `a` does not allow it to. -/
def Audience.refusal (what : String) : Audience → String
  | .within m => s!"{what} is internal to {shownModule m}: mark it <public> to use it outside (Book of Verse ch. 12)"
  | .scoped m gs => s!"{what} is scoped to {", ".intercalate ((m :: gs).eraseDups.map shownModule)}: only code there may use it (Book of Verse ch. 12)"
  | .below c => s!"{what} is <protected>: only {shown c} and the classes below it may use it (Book of Verse ch. 12)"
  | .inClass c => s!"{what} is <private>: only {shown c}'s own code may use it (Book of Verse ch. 12)"
  | a => s!"{what} is {a.what} (Book of Verse ch. 12)"

/-- Why code at `site` may not use `what`, a definition whose effective
    audience is `e` (its own first, then those of the definitions it is in,
    `around` naming the nearest), if it may not. -/
def Eff.refusal (below : String → String → Bool) (site : Site) (e : Eff) (what : String)
    (around : String := "") : Option String :=
  (e.denial below site).map fun a =>
    if e.head? == some a || around.isEmpty then a.refusal what
    else s!"{what} cannot be used here: " ++ a.refusal around


/-- The classes and interfaces each class of a resolved program is below,
    itself first. -/
def hierarchy (tops : List STop) : String → List String :=
  let parents : Std.HashMap String (List String) := tops.foldl (fun m t => match t with
    | .classDef _ c _ _ _ ps .. => m.insert c (ps.filterMap fun | .name q | .app q _ => some q | _ => none)
    | _ => m) {}
  fun c => Id.run do
    let mut seen : List String := []
    let mut todo := [c]
    for _ in [0:parents.size + 2] do
      let mut next := []
      for x in todo do
        if !seen.contains x then
          seen := seen ++ [x]
          next := next ++ parents.getD x []
      if next.isEmpty then break
      todo := next
    return seen

/-- Every expression of a definition, its own code with its parameters'
    defaults and its fields' defaults, each with the site it is in. -/
def codeOf : STop → List (Site × SExpr)
  | .fn _ n ps _ _ _ body =>
    let s : Site := { module := moduleOfName n }
    (body :: ps.filterMap (·.default)).map (s, ·)
  | .const _ n _ _ body =>
    let s : Site := { module := moduleOfName n }
    match body with
    | .structDef _ _ _ fs => fs.filterMap fun f => f.default.map (s, ·)
    | b => [(s, b)]
  | .classDef _ c _ _ _ _ _ fs ms =>
    let s : Site := { module := moduleOfName c, cls := some c }
    fs.filterMap (fun f => f.default.map (s, ·)) ++ ms.flatMap fun
      | .fn _ _ ps _ _ _ body => (body :: ps.filterMap (·.default)).map (s, ·)
      | _ => []

/-- The constructions `c{F := e, …}` in an expression: where, the type, the
    fields given. -/
partial def constructions : SExpr → List (Pos × String × List (Pos × String))
  | e@(.construct p n _ fs) =>
    (p, n, fs.filterMap fun | .decl fp f .. => some (fp, f) | _ => none) :: e.children.flatMap constructions
  | .structDef _ _ _ fs => fs.flatMap fun f => (f.default.map constructions).getD []
  | e => e.children.flatMap constructions

/-- The uses of a resolved program that name a class's constructor or members
    without a value's type: each construction `c{F := e, …}` and constructor
    function `F<constructor>(…) := c:` needs `c`'s constructor and each field
    it gives to allow it (Book of Verse tests, ArchetypeAccessSpecifiers;
    ch. 12 example 15: a field given is read); a class's parents' constructors
    allow it (`class<internal>` "forces folks outside the owning module to
    use a constructor function", and subclassing does not get around it); and
    an override overrides a member its class may use (Book of Verse tests,
    AccessLevelInheritance: 3593). -/
def checkUses (env : Env) (tops : List STop) : Except String Unit := do
  let above := hierarchy tops
  let interfaces : List String := tops.filterMap fun | .classDef _ c _ _ _ _ true .. => some c | _ => none
  let below (c d : String) : Bool := (above c).contains d
  let construct (site : Site) (p : Pos) (c : String) (fields : List (Pos × String)) : Except String Unit := do
    if c.startsWith "$" then return
    if let some e := env.ctors[c]? then
      if let some a := e.denial below site then
        throw (s!"{p.show}: {shown c}\{…} constructs {shown c} here: " ++ a.refusal s!"the constructor of {shown c}")
    for (fp, f) in fields do
      if let some mem := env.member? (above c) f then
        if let some why := mem.read.refusal below site s!"the field {f} of {shown mem.cls}" (shown mem.cls) then
          throw s!"{fp.show}: {why}"
  for t in tops do
    for (site, e) in codeOf t do
      for (p, c, fs) in constructions e do construct site p c fs
    match t with
    | .fn p n _ _ specs _ body =>
      -- (a constructor function's items give its class's fields)
      if let some cs := specs.find? (·.startsWith "$constructor:") then
        let c := (cs.drop "$constructor:".length).toString
        let fs := match body with
          | .block _ items => items.filterMap fun | .decl fp f .. => some (fp, f) | _ => none
          | _ => []
        construct { module := moduleOfName n } p c fs
    | .classDef p c _ _ _ parents _ fields methods =>
      let site : Site := { module := moduleOfName c, cls := some c }
      for q in parents.filterMap (fun | .name q | .app q _ => some q | _ => none) do
        if let some e := env.ctors[q]? then
          if let some a := e.denial below site then
            if interfaces.contains q then
              throw (s!"{p.show}: {shown c} cannot implement {shown q} here: " ++ a.refusal s!"implementing {shown q} (interface<…>)")
            throw (s!"{p.show}: {shown c} cannot be below {shown q}, as subclassing constructs it: " ++ a.refusal s!"the constructor of {shown q}")
      let overrides := fields.filterMap (fun f => if f.isOverride then some (p, f.name) else none) ++
        methods.filterMap fun | .fn mp mn _ _ ms .. => if ms.contains "override" then some (mp, mn) else none
                              | _ => none
      for (mp, m) in overrides do
        if let some mem := env.member? ((above c).drop 1) m then
          if let some a := mem.read.denial below site then
            throw (s!"{mp.show}: {bareName m}<override> in {shown c} overrides what {shown c} cannot use: " ++ a.refusal s!"{bareName m} of {shown mem.cls}")
    | _ => pure ()


end OpenVerse.Front.Access

namespace OpenVerse.Front.Access

/-- The type definitions of a program, by qualified name: its classes,
    interfaces, structs, enums, refinement types and type aliases. -/
def typeDefs (tops : List STop) : Std.HashSet String :=
  let named : Std.HashSet String := tops.foldl (fun s t => match t with
    | .classDef _ n .. => s.insert n
    | .const _ n _ none (.structDef ..) | .const _ n _ none (.enumDef ..)
    | .const _ n _ none (.refineDef ..) | .const _ n _ none (.typeAlias ..) => s.insert n
    | _ => s) {}
  -- (an alias `a := c`, written as a value could be: the aliases' pass decides)
  tops.foldl (fun s t => match t with
    | .const _ n _ none e => match e.asType? with
      | some ty => if ty.names.any named.contains then s.insert n else s
      | none => s
    | _ => s) named

/-- A definition `what` whose effective audience is `e`, at `p`, names the
    types `tys`: each of the program's (`defs`) is at least as visible
    (Book of Verse tests, DigestVisibility: "dependencies of definitions are
    as accessible as the definitions themselves", 3593; ch. 11: "A type alias
    cannot be more public than the type it aliases"). -/
def checkExposes (lv : Levels) (defs : Std.HashSet String) (below : String → String → Bool)
    (p : Pos) (what : String) (e : Eff) (tys : List STy) (bound : List String := []) : Except String Unit := do
  for t in tys do
    for n in t.names do
      if bound.contains n || !defs.contains n then continue
      let et := lv.definition n
      if !e.inside below moduleOfName et then
        -- (the type's own level, or that of a module it is in, `m.take i`)
        let i := (et.findIdx? fun b => !e.any (·.inside below moduleOfName b)).getD 0
        let a := et.getD i .everyone
        let where_ := if i == 0 then s!"{shown n} is {a.what}"
          else s!"{shown n} is in {shownModule ((moduleOfName n).take i)}, which is {a.what}"
        throw s!"{p.show}: {what} names {shown n}, which is less visible: {where_}, and a definition exposes nothing less visible than itself (Book of Verse tests, DigestVisibility, TypeAlias)"

/-- The aliases of a resolved program, before they are written out: each
    `a<access> := t` is no more visible than what `t` names (Book of Verse
    ch. 11). -/
def checkAliases (lv : Levels) (tops : List STop) : Except String Unit := do
  let defs := typeDefs tops
  let below := fun (_ _ : String) => false
  for t in tops do
    if let .const p n _ none body := t then
      if !defs.contains n then continue
      let (tps, ty?) : List String × Option STy := match body with
        | .typeAlias _ tps ty => (tps.map (·.name), some ty)
        | .structDef .. | .enumDef .. | .refineDef .. => ([], none)
        | e => ([], e.asType?)
      if let some ty := ty? then
        checkExposes lv defs below p s!"the type alias {shown n}" (lv.definition n) [ty] tps

/-- The consistency rules of a resolved program, its aliases written out:
    a definition's signature names nothing less visible than the definition
    (a function's or method's parameters, result and type parameters'
    bounds, a constant's or field's type, a struct's fields; an override is
    judged in its own class, AccessLevelInheritance.versetest:863), a
    class's or interface's field with no default is at least as visible as
    its constructor, which must give it a value (Classes/AccessSpecifiers
    410-433), and a field's var is at least as restrictive as reading it
    (ch. 12, "The write specifier must be at least as restrictive as the read
    specifier"). -/
def checkConsistency (lv : Levels) (tops : List STop) : Except String Unit := do
  let defs := typeDefs tops
  let above := hierarchy tops
  let below (c d : String) : Bool := (above c).contains d
  let hidden (n : String) : Bool :=
    let last := (n.splitOn "::").getLastD n
    last.startsWith "$" && !last.startsWith extensionPrefix
  -- (each member's level: written, or, for an override, that of what it overrides)
  let declared : Std.HashMap String (Option String) := tops.foldl (fun m t => match t with
    | .classDef _ c _ _ _ _ _ fs ms =>
      let m := fs.foldl (fun m f => if f.isOverride then m else m.insert s!"{c}.{bareName f.name}" (levelOf f.specs)) m
      ms.foldl (fun m x => match x with
        | .fn _ mn _ _ sp .. => if sp.contains "override" then m else m.insert s!"{c}.{bareName mn}" (levelOf sp)
        | _ => m) m
    | _ => m) {}
  let levelIn (c x : String) (written : Option String) (isOverride : Bool) : Option String :=
    if !isOverride then written
    else ((above c).drop 1).findSome? (fun d => declared[s!"{d}.{bareName x}"]?) |>.getD none
  for t in tops do
    match t with
    | .fn p n ps tps specs ret _ =>
      if hidden n then continue
      checkExposes lv defs below p s!"{shown n}" (lv.definition n)
        (ret :: ps.map (·.ty) ++ tps.filterMap (·.upperBound)) (tps.map (·.name))
    | .const p n _ (some ty) _ =>
      if hidden n then continue
      checkExposes lv defs below p s!"{shown n}" (lv.definition n) [ty]
    | .const p n _ none (.structDef _ tps _ fs) =>
      checkExposes lv defs below p s!"the struct {shown n}" (lv.definition n) (fs.map (·.ty)) (tps.map (·.name))
    | .classDef p c _ tps specs _ _ fs ms =>
      if hidden c then continue
      let m := moduleOfName c
      let ce := lv.definition c
      let ctor := ctorEff specs m c ++ ce
      let memberEff (lvl : Option String) : Eff :=
        audience lvl m (some c) :: (if lvl == some "protected" then ctor else ce)
      let cps := tps.map (·.name)
      for f in fs do
        let lvl := levelIn c f.name (levelOf f.specs) f.isOverride
        checkExposes lv defs below p s!"the field {bareName f.name} of {shown c}" (memberEff lvl) [f.ty] cps
        if f.default.isNone && !f.isOverride && !(ctor.inside below moduleOfName (memberEff lvl)) then
          let a := (memberEff lvl).headD .everyone
          throw s!"{p.show}: the field {bareName f.name} of {shown c} has no default, so a construction gives it one, but it is {a.what} where {shown c}'s constructor is wider: give it a default, or an access at least as visible as the constructor (Book of Verse tests, Classes/AccessSpecifiers)"
        -- (judged as the others, with what the field is in: in an internal
        -- class, var<public> X<internal> is set where it is read)
        if let some w := levelOf f.varSpecs then
          let r := audience (levelOf f.specs) m (some c)
          if !Eff.inside below moduleOfName (audience (some w) m (some c) :: ce) (r :: ce) then
            throw s!"{p.show}: var<{w}> {bareName f.name}: setting it is more visible than reading it, {r.what}; the write access is at least as restrictive as the read access (Book of Verse ch. 12)"
      -- (a method's overloads have one access: a use reaches them by name)
      let methodLevels := ms.filterMap fun
        | .fn mp mn _ _ sp .. => if sp.contains "override" || mn.startsWith "$" then none else some (mp, bareName mn, levelOf sp)
        | _ => none

      for (mp, mn, l) in methodLevels do
        if methodLevels.any fun (_, n, k) => n == mn && k != l then
          throw s!"{mp.show}: the overloads of {shown c}.{mn} must all have one access level"
      for x in ms do
        if let .fn mp mn mps mtps mspecs mret _ := x then
          if mn.startsWith "$" then continue

          let lvl := levelIn c mn (levelOf mspecs) (mspecs.contains "override")
          checkExposes lv defs below mp s!"the method {bareName mn} of {shown c}" (memberEff lvl)
            (mret :: mps.map (·.ty) ++ mtps.filterMap (·.upperBound)) (cps ++ mtps.map (·.name))
    | _ => pure ()

end OpenVerse.Front.Access
