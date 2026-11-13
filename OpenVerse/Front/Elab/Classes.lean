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

/-- Class `n`'s fields (`Fields.map`); none for a name that is not a class's. -/
def Fields.of (fields : Fields) (n : String) : List (String × STy × Option SExpr × Bool) :=
  fields.map[n]?.getD []

/-- The fields of the classes, a phase of `elabProgramCore`: each class's,
    inherited ones first (from its superclass, then from the interfaces above
    it, once each, with the default of the most specific interface that gives
    one), then its own, which do not take an inherited field's or method's
    name unless they override a field, then hidden fields that hold values of
    its type parameters where a dispatch needs them (#209, #250, #276, #351,
    and all of them for the classes in `requests.witnesses`). -/
def classFields (classes : Classes) (requests : Requests) : Except String Fields := do
  -- the fields of each class: its superclass's, then those of the
  -- interfaces above it that are not there yet (once, along a diamond), then
  -- its own (an `<override>` field gives an inherited one a new default)
  let mut full : Array (String × List (String × STy × Option SExpr × Bool)) := #[]
  let mut fieldOverrides : Array (Pos × String × String × STy) := #[]
  let mut defaultClashes : Array String := #[]
  -- (each class's fields by name too: lookups in `full` made this cubic)
  let mut fullMap : Std.HashMap String (List (String × STy × Option SExpr × Bool)) := {}
  for _ in [0:classes.defs.length + 1] do
    -- (until a pass resolves nothing more, or every class is resolved)
    if full.size == classes.defs.length then break
    let before := full.size
    for cd in classes.defs do
      if fullMap.contains cd.name then continue
      let inherited? : Option (List (String × STy × Option SExpr × Bool)) :=
        match (classes.henv.info cd.name).parent with
        | none => some []
        | some q =>
          -- in terms of this class's type parameters (#39)
          let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
          let σ := ((((classes.cdef? q).map (·.tps)).getD []).map (·.name)).zip qargs
          fullMap[q]?.map fun fs => fs.map fun (f, sty, d, v) => (f, sty.substNames σ, d, v)
      let some inh := inherited? | continue
      -- the interfaces above must be resolved first
      let ifacesUp := ((classes.henv.supers cd.name).drop 1).filter (classes.henv.info · |>.isIface)
      if ifacesUp.any (fun i => !fullMap.contains i) then continue
      let mut fs : List (String × STy × Option SExpr × Bool) := inh
      -- each interface field not inherited through the class chain, once; its
      -- default is that of the most specific interface that gives one (as for
      -- methods, whatever the order of the parents)
      for i in ifacesUp do
        -- (in terms of this class's type parameters, #53)
        let iσ := ((((classes.cdef? i).map (·.tps)).getD []).map (·.name)).zip ((classes.supArgsSTy cd.name i).getD [])
        for (f, sty0, _, isVar) in fullMap[i]?.getD [] do
          let sty := sty0.substNames iσ
          if ((classes.henv.supers cd.name).drop 1).any (classes.declares · f) then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
          if let some (_, _, _, v0) := fs.find? (·.1 == f) then
            -- reached again: its type must agree (checked once types are
            -- resolved), and whether it is a var
            if v0 != isVar then
              throw s!"{cd.pos.show}: {cd.name} inherits field '{f}' as a var from one parent and not from another"
            fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
          else
            -- the interfaces that give the field a default themselves (an
            -- inherited default is its declaring interface's)
            let ownDefault (j : String) : Option SExpr :=
              (((classes.cdef? j).map (·.fields)).getD []).findSome? fun (g, _, d, _) => if g == f then d else none
            let withDefault := ifacesUp.filter fun j => (ownDefault j).isSome
            let best := withDefault.filter fun j => !withDefault.any fun j' => j' != j && classes.henv.isSub j' j
            if best.length > 1 && !cd.overrides.contains f then
              defaultClashes := defaultClashes.push
                s!"{cd.pos.show}: {cd.name} inherits a default for field '{f}' from both {best[0]!} and {best[1]!}: give it one with {f}<override>:t = e"
            let d := best.head?.bind ownDefault
            fs := fs ++ [(f, sty, d, isVar)]
      for (f, sty, d, isVar) in cd.fields do
        if f == "Self" then throw s!"{cd.pos.show}: a field of {cd.name} cannot be called Self"
        if ((classes.henv.supers cd.name).drop 1).any (classes.declares · f) then
          throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
        match fs.findIdx? (fun (g : String × STy × Option SExpr × Bool) => g.1 == f) with
        | some k =>
          if cd.overrides.contains f && d.isNone then
            throw s!"{cd.pos.show}: {f}<override> must give a new default: write {f}<override>:t = e"
          if !cd.overrides.contains f then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited field (write {f}<override>:t = … to give it a new default)"
          let (_, sty0, _, v0) := fs[k]!
          if isVar != v0 then
            throw s!"{cd.pos.show}: {f}<override> cannot change whether the field is a var"
          fs := fs.set k (f, sty0, d, v0)
          fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
        | none =>
          if cd.overrides.contains f then
            throw s!"{cd.pos.show}: {f}<override> in {cd.name} does not override an inherited field"
          fs := fs ++ [(f, sty, d, isVar)]
      -- (#209) each type parameter that is not one of its parent's type
      -- arguments as a whole: a hidden field holds a value of it, from
      -- which a method of the class, run by a dispatch that opens it, gets
      -- its slots of that type (`Sig.selfTps`)
      -- (only where an override, at or below, may need it)
      let methodsBelow := classes.defs.any fun cd' => classes.henv.isSub cd'.name cd.name &&
        cd'.methods.any fun | .fn _ _ _ _ effs .. => effs.contains "override" | _ => false
      -- (#250: or a cast that opens them targets the class or one below it,
      -- whose branch's function reads them from the object, also those an
      -- ancestor of the target adds)
      let methodsBelow := methodsBelow || requests.witnesses.contains cd.name ||
        requests.casts.any fun l => !l.opened.isEmpty && classes.henv.isSub l.target cd.name
      -- (#276, #209: a root class counts them as `rootArgCount` does: the
      -- first of its Verse Core type arguments, as many as the interface
      -- with the fewest type parameters at or above it, or above a class
      -- below it that leaves one of the others a type parameter; an
      -- interface has no such fields)
      let qargs? : Option (List STy) := if cd.isIface then none else
        if requests.witnesses.contains cd.name then some [] else match (classes.henv.info cd.name).parent with
        | some q => some (((cd.parents.zip cd.parentArgs).lookup q).getD [])
        | none =>
          -- (the interfaces above it or above a class below it, #209)
          let below := classes.defs.filter fun c => !c.isIface && classes.henv.isSub c.name cd.name
          let ifs := classes.defs.filter fun i => i.isIface && below.any fun c => classes.henv.isSub c.name i.name
          if ifs.isEmpty then none else
          -- (its Verse Core type arguments: those it gives the interface it
          -- lists with the most, then its other type parameters, as
          -- `coreArgs` has them; all of them when it lists no interface)
          -- (each at that interface's Verse Core type arguments, also those
          -- it gives its own parents, #53)
          let longest := ((cd.parents.zip cd.parentArgs).filter fun (q, _) => (classes.henv.info q).isIface).foldl
            (fun (b : List STy) (q, qa) =>
              let qa := match classes.defs.find? (·.name == q) with
                | some qd => qd.ifaceCoreS classes.defs qa
                | none => qa
              if b.length < qa.length then qa else b) []
          let others := cd.tps.filter fun tp => !longest.any fun | .name v => v == tp.name | _ => false
          let coreS := longest ++ others.map fun tp => STy.name tp.name
          -- (#351: an interface it lists at type arguments that are not a
          -- prefix of its own is referred to through views, a dispatch
          -- through which may open any of them: all have hidden fields)
          let nonPrefix := (cd.parents.zip cd.parentArgs).any fun (q, qa) =>
            (classes.henv.info q).isIface &&
              let ca := match classes.defs.find? (·.name == q) with
                | some qd => qd.ifaceCoreS classes.defs qa
                | none => qa
              !(ca.length ≤ coreS.length && (ca.zip coreS).all fun (a, b) => Choice.styEq a b)
          if nonPrefix then some [] else
          -- (as a class below gives them: through its parents' arguments)
          let rec viewIn (fuel : Nat) (c : CDef) : List STy :=
            match fuel with
            | 0 => coreS
            | f + 1 =>
              if c.name == cd.name then coreS else
              match (classes.henv.info c.name).parent with
              | some q => match classes.defs.find? (·.name == q) with
                | some qd =>
                  let σ := qd.tps.map (·.name) |>.zip (((c.parents.zip c.parentArgs).lookup q).getD [])
                  (viewIn f qd).map (·.substNames σ)
                | none => coreS
              | none => coreS
          -- (an interface above a class below it counts only when one of
          -- its type arguments that interface does not give is still a
          -- type parameter there, as `rootArgCount` has it, #276)
          let fewest := below.foldl (fun m c =>
            let view := viewIn classes.defs.length c
            (ifs.filter fun i => classes.henv.isSub c.name i.name).foldl (fun m i =>
              let k := i.tps.length
              if c.name == cd.name || (view.drop k).any (STy.mentionsAny (c.tps.map (·.name))) then min m k else m) m)
            coreS.length
          some (coreS.take fewest)
      if let some qargs := qargs? then
        for tp in (if methodsBelow then cd.tps else []) do
          -- (all of them for a class with a class parent that lists an
          -- interface at type arguments that are not a prefix of its own,
          -- which a dispatch through a view opens, #351)
          if requests.witnesses.contains cd.name || !qargs.any (fun | .name v => v == tp.name | _ => false) then
            fs := fs ++ [(s!"$w.{cd.name}.{tp.name}", .name tp.name, some (.ident cd.pos "$witness"), false)]
      full := full.push (cd.name, fs)
      fullMap := fullMap.insert cd.name fs
    if full.size == before then break
  let fields : Fields := { map := fullMap, overrides := fieldOverrides, defaultClashes }
  for cd in classes.defs do
    for (f, _, _, _) in fields.of cd.name do
      if (classes.henv.supers cd.name).any (classes.declaresBase · f) then
        throw s!"{cd.pos.show}: '{f}' is both a field and a method of {cd.name}"
  return fields

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
