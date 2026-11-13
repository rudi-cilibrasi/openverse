/- Elaboration of a program's classes and interfaces (phases 4–6 of `elabProgramCore`);
   public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering

namespace OpenVerse.Front
open OpenVerse

/-- The classes and interfaces of a program, and their hierarchy (`classHierarchy`). -/
structure Classes where
  /-- Their definitions, in the program's order. -/
  defs : List CDef
  /-- Their hierarchy, as a type environment has it: each one's parent and
      interfaces (`TyEnv.cinfo`) and the classes above it (`TyEnv.supersMap`). -/
  henv : TyEnv

/-- The class or interface named `n`. -/
def Classes.cdef? (classes : Classes) (n : String) : Option CDef := classes.defs.find? (·.name == n)

/-- `cd`'s method named `m` (as elaborated: an overload is `M$ovN`, #106). -/
def CDef.methodNamed (cd : CDef) (m : String) : Option STop := cd.methods.find? fun
  | .fn _ x .. => x == m
  | _ => false

/-- Whether class or interface `n` declares a method named `m` itself. -/
def Classes.declares (classes : Classes) (n m : String) : Bool :=
  ((classes.cdef? n).bind (CDef.methodNamed · m)).isSome

/-- Whether `n` declares a method `m` itself, by the name as written (an
    overload's is its method's, #106). -/
def Classes.declaresBase (classes : Classes) (n m : String) : Bool :=
  ((classes.cdef? n).map fun cd => cd.methods.any fun
    | .fn _ x .. => methodBase x == m
    | _ => false).getD false

/-- Whether `n` declares a method `m` itself with a body (not abstract). -/
def Classes.hasBody (classes : Classes) (n m : String) : Bool :=
  match (classes.cdef? n).bind (CDef.methodNamed · m) with
  | some (.fn _ _ _ _ effs _ _) => !effs.contains "$abstract"
  | _ => false

/-- The type arguments `c` gives `T` above it, as written in terms of `c`'s
    type parameters (through parents of both kinds, #39, #53). -/
def Classes.supArgsSTy (classes : Classes) (c T : String) : Option (List STy) := Id.run do
  let mut frontier : List (String × List STy) :=
    [(c, ((classes.cdef? c).map fun cd => cd.tps.map fun tp => STy.name tp.name).getD [])]
  for _ in [0:classes.defs.length + 1] do
    if let some (_, a) := frontier.find? (·.1 == T) then return some a
    frontier := frontier.flatMap fun (x, xa) => match classes.cdef? x with
      | some xd =>
        let σ := (xd.tps.map (·.name)).zip xa
        (xd.parents.zip xd.parentArgs).map fun (q, qa) => (q, qa.map (·.substNames σ))
      | none => []
  return none

/-- The class hierarchy, a phase of `elabProgramCore`: the classes and
    interfaces of `tops` (#14, #18), each one's parent and interfaces, which
    must exist, take the type arguments given, and inherit as classes and
    interfaces may (a class from one class, no interface from a class, none
    from a `<final>` one, none from itself); and each class's construction
    effects `constructionFx` allow those its parents declare. -/
def classHierarchy (tops : List STop) (constructionFx : Std.HashMap String (List String)) :
    Except String Classes := do
  -- classes and interfaces (#14, #18): each is a struct whose fields are
  -- those inherited first, then its own; each method `M` of `c` a function
  -- `c.M` whose first parameter is `Self`, generic over the class's type
  -- parameters and then its own; an abstract method one whose body is
  -- unreachable
  let cdefs : List CDef := tops.filterMap fun
    | .classDef p n tps specs parents isIface fields overrides methods =>
      let names := parents.map fun | .name q => q | .app q _ => q | _ => "?"
      let args := parents.map fun | .app _ as => as | _ => []
      some { pos := p, name := n, tps, specs, parents := names, parentArgs := args, isIface, fields,
             overrides, methods }
    | _ => none
  -- the hierarchy
  let mut cinfo : Array (String × ClassInfo) := #[]
  for cd in cdefs do
    let p := cd.pos
    for sp in cd.specs do
      match sp with
      | "persistable" | "final_super" => throw s!"{p.show}: <{sp}> classes are not supported yet (#11)"
      | _ => pure ()
    let mut parent : Option String := none
    let mut ifaces : Array String := #[]
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      let some qd := cdefs.find? (·.name == q)
        | if tops.any (fun | .const _ n' none (.structDef ..) => n' == q | _ => false) then
            throw s!"{p.show}: {q} is a struct: only classes and interfaces can be inherited from"
          else throw s!"{p.show}: unknown class or interface '{q}'"
      if qargs.length != qd.tps.length then
        throw s!"{p.show}: {q} takes {qd.tps.length} type argument(s), found {qargs.length}"
      -- (an interface that extends a parametric interface may give it any
      -- type arguments: its Verse Core type arguments start with that
      -- interface's at them, as a class's start with its parent's, #53)

      if qd.isIface then ifaces := ifaces.push q
      else
        if cd.isIface then throw s!"{p.show}: interface {cd.name} cannot extend class {q}"
        if parent.isSome then throw s!"{p.show}: class {cd.name} has two superclasses (a class inherits from at most one)"
        if qd.specs.contains "final" then throw s!"{p.show}: class {q} is <final>: it cannot be inherited from"
        parent := some q
    let info : ClassInfo := { parent, ifaces := ifaces.toList, isIface := cd.isIface,
                              isAbstract := cd.specs.contains "abstract", isFinal := cd.specs.contains "final" }
    cinfo := cinfo.push (cd.name, info)
  let henv : TyEnv := { classes := cdefs.map (·.name), cinfo := cinfo.toList,
                        cinfoMap := cinfo.foldl (fun m (n, i) => m.insert n i) {} }
  let henv : TyEnv := { henv with supersMap := henv.classes.foldl (fun m d => m.insert d (henv.supers d)) {} }
  let directUp (n : String) : List String := (henv.info n).parent.toList ++ (henv.info n).ifaces
  for cd in cdefs do
    let mut seen : List String := []
    let mut frontier := directUp cd.name
    for _ in [0:cdefs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap directUp
    if seen.contains cd.name then throw s!"{cd.pos.show}: {cd.name} inherits from itself"
  for cd in cdefs do
    if let some allowed := constructionFx[cd.name]? then
      for parent in cd.parents do
        if let some required := constructionFx[parent]? then
          for effect in required do
            if !allowed.contains effect then
              throw s!"{cd.pos.show}: construction of {cd.name} must allow <{effect}> declared by parent {parent}; add <{effect}> or <transacts> to {cd.name}"
  return { defs := cdefs, henv }

/-- The fields of the classes and interfaces. -/
structure Fields where
  /-- Each class's fields, by its name: its superclass's, then those of the
      interfaces above it that are not there yet, then its own, then hidden
      ones that hold values of its type parameters (#209); each with its
      type, its default and whether it is a `var`. -/
  map : Std.HashMap String (List (String × STy × Option SExpr × Bool))
  /-- The inherited fields a class gives again (`<override>`, or reached through
      two parents), with the type it gives them: `checkSignatures` checks, once
      types are resolved, that it is the inherited one. -/
  overrides : Array (Pos × String × String × STy)
  /-- A refusal for each field that two interfaces give defaults, which
      `checkSignatures` gives after the signature checks. -/
  defaultClashes : Array String

/-- The classes' methods and constructors, as functions. -/
structure Methods where
  /-- The program's definitions with each class expanded: a struct of its
      fields, and each method `M` a function `c.M` whose first parameter is
      `Self`; and each constructor its functions (`expandCtors`). -/
  tops : List STop
  /-- The methods that are a family's stub (`Choice.familyStub`), as functions,
      each where it is declared. -/
  stubs : List (String × Pos)
  /-- The abstract methods, each with its class. -/
  abstracts : Array (String × String)
  /-- Each override where it is, as `c.M`, with the method `q.M` it overrides. -/
  overridePairs : Array (Pos × String × String)
  /-- Each implementation `e.M` a concrete class `c` uses for a declaration
      `q.M` above it, with `c`'s position: `checkSignatures` checks they agree. -/
  implChecks : Array (Pos × String × String × String)

end OpenVerse.Front
