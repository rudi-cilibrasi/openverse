/- Fields with accessors: a read, a `set` and a construction of one, as calls
   of its class's methods (Book of Verse ch. 10, "Fields with Accessors";
   `Front/Accessors.lean` checks the declarations; the rules are in
   docs/research/accessors.md). -/
import OpenVerse.Front.Elab.Control
import OpenVerse.Front.Accessors

namespace OpenVerse.Front
open OpenVerse

/-- A step of a place, after its root: a member `.F` (`inl`) or an index or
    key `[K]` (`inr`), with its position. -/
abbrev PlaceStep := Pos × Sum String SExpr

/-- A place as its root and the steps after it, `T.AS[0].I` as `T` and
    `.AS`, `[0]`, `.I`. -/
partial def placeSteps : SExpr → SExpr × Array PlaceStep
  | .member p e f => let (r, ss) := placeSteps e; (r, ss.push (p, .inl f))
  | .app p e [k] true => let (r, ss) := placeSteps e; (r, ss.push (p, .inr k))
  | e => (e, #[])

/-- The place a root and steps write. -/
def placeOf (root : SExpr) (steps : List PlaceStep) : SExpr :=
  steps.foldl (fun e (p, s) => match s with
    | .inl f => .member p e f
    | .inr k => .app p e [k] true) root

/-- The field with accessors `f` (`(q:)f`: the one `q` declares) of a value
    of `c(targs)`, at the value's type arguments. -/
def TyEnv.accessorOf? (env : TyEnv) (c : String) (targs : List Ty) (f : String) :
    Option (AccessorField × Ty) := do
  let (q, f) := (splitQual? f).getD ("", f)
  let a ← env.accessors.find? fun a => a.name == f && env.isSub c a.owner && (q.isEmpty || a.owner == q)
  let σ := (((env.sparams.lookup a.owner).getD []).map (·.1)).zip (env.upArgs c targs a.owner)
  return (a, a.ty.subst σ)

/-- The value of a step into a value of `t` that is not an object: an
    array's or a string's element, a map's value, a struct's field. -/
def accessorStepTy? (env : TyEnv) (t : Ty) (step : Sum String SExpr) : Option Ty :=
  match t, step with
  | .arr e, .inr _ => some e
  | .map _ v, .inr _ | .weakMap _ v, .inr _ => some v
  | .struct n targs, .inl f =>
    if env.classes.contains n then none else ((env.fields n targs).find? (·.1 == f)).map (·.2.1)
  | _, _ => none

/-- How far a path into a field's value of type `t` goes on: the steps it
    takes, each into a value (`accessorStepTy?`), with the value's type
    after them. -/
def accessorPath (env : TyEnv) (t : Ty) (steps : List PlaceStep) : List PlaceStep × Ty :=
  go steps [] t
where
  go : List PlaceStep → List PlaceStep → Ty → List PlaceStep × Ty
    | [], acc, t => (acc.reverse, t)
    | s :: rest, acc, t =>
      match accessorStepTy? env t s.2 with
      | some u => go rest (s :: acc) u
      | none => (acc.reverse, t)

/-- A place that reaches a field with accessors: the expression whose value
    has it (an object), the field and its type there, how the place names it
    (`X` or `(q:)X`), and the steps after it. -/
structure AccessorPlace where
  recv : SExpr
  cls : String
  field : AccessorField
  ty : Ty
  written : String
  pos : Pos
  steps : List PlaceStep
  /-- A field `cls` has with storage, which classes below give accessors
      (`var X<override><getter(G)><setter(S)>`, Book of Verse tests,
      InterfaceWithAccessors.versetest:24-40): those classes, each with the
      field there. Empty when `cls` has the field with accessors itself. -/
  overrides : List (String × AccessorField) := []

/-- The type of `e` (an elaboration that keeps nothing), if it has one. -/
def typeOf? (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (e : SExpr) : EM (Option Ty) := do
  let st ← get
  let r ← tryCatch (some <$> elabE { ctx with typeOnly := true } e none) (fun _ => pure none)
  set st
  return r.map (·.ty)

/-- The places within `root` and `steps` that reach a field with accessors,
    from the root on (each a field of its receiver's class or interface,
    a bare name in a method a field of `Self`'s). Only names some class
    gives accessors are looked at. -/
def accessorPlaces (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (root : SExpr)
    (steps : Array PlaceStep) : EM (List AccessorPlace) := do
  let env := ctx.types
  let named (f : String) : Bool :=
    let f := ((splitQual? f).map (·.2)).getD f
    env.accessors.any (·.name == f)
  let mut out : Array AccessorPlace := #[]
  -- (a bare name in a method: `Self`'s field)
  if let .ident p n := root then
    if named n && (ctx.lookup n).isNone && ctx.selfClass.isSome then
      if let some (.struct c targs) ← typeOf? elabE ctx (.ident p "Self") then
        if let some (a, t) := env.accessorOf? c targs n then
          out := out.push { recv := .ident p "Self", cls := c, field := a, ty := t, written := n, pos := p,
                            steps := steps.toList }
  for ((p, step), i) in steps.toList.zipIdx do
    let .inl f := step | continue
    if !named f then continue
    let recv := placeOf root (steps.toList.take i)
    if let some (.struct c targs) ← typeOf? elabE ctx recv then
      if let some (a, t) := env.accessorOf? c targs f then
        out := out.push { recv, cls := c, field := a, ty := t, written := f, pos := p, steps := steps.toList.drop (i + 1) }
      else if let some (_, t, _) := (env.fields c targs).find? (·.1 == f) then
        -- (a field with storage here, with accessors in classes below)
        let overrides := (env.concreteBelow c).filterMap fun d =>
          if d == c then none else (env.accessorOf? d [] f).map fun (a, _) => (d, a)
        if let some (_, a) := overrides.head? then
          if overrides.any fun (d, _) => !((env.sparams.lookup d).getD []).isEmpty then
            eerr p s!"{f} of {c} is a field with accessors in a class below it with type parameters: reading or setting it through {c} is not supported yet"
          out := out.push { recv, cls := c, field := a, ty := t, written := f, pos := p,
                            steps := steps.toList.drop (i + 1), overrides }
  return out.toList

/-- The struct value an accessor is passed, `(:accessor)`. -/
def accessorArg (p : Pos) : SExpr := .construct p Accessors.accessorStruct [] []

/-- A step of a path as an argument of an accessor: an index or key as
    written, a struct's field by its name, a string (Book of Verse tests,
    DeepMutabilityForCustomClassVarAccessors.versetest:365-375). -/
def accessorStepArg : PlaceStep → SExpr
  | (_, .inr k) => k
  | (p, .inl f) => .str p [.text f]

/-- The overloads of method `m` that a value of class `c` has, by their
    signatures (`Self` first). -/
def methodSigs (ctx : Ctx) (c m : String) : List Sig :=
  let names := (ctx.types.methodOverloads.lookup m).getD [m]
  names.filterMap fun o => (ctx.methodDecl? c o).bind fun owner => ctx.sig? s!"{owner}.{o}"

/-- The accessor `m` of `place` that takes `n` arguments after the accessor:
    whether it is `<decides>`; refused when `c` has none. -/
def accessorDecides (ctx : Ctx) (p : Pos) (place : AccessorPlace) (kind m : String) (n : Nat) : EM Bool := do
  let sigs := (methodSigs ctx place.cls m).filter (·.params.length == n + 2)
  let some s := sigs.head?
    | eerr p s!"{place.written} is a field with accessors: this {if kind == "setter" then "set" else "read"} calls its {kind} {m} with {n} argument(s) after the accessor (the path's indices and field names{if kind == "setter" then ", then the value" else ""}), and {place.cls} has no such {m} (Book of Verse ch. 10, \"Fields with Accessors\")"
  if s.decides && !ctx.canFail then
    eerr p s!"{place.written} is a field with accessors whose {kind} {m} for this path can fail: use it in a failure context"
  return s.decides

/-- The context of a call of an accessor the elaboration writes for a use of
    a field: marked, so that the accessor's own access does not judge it
    (`Ctx.accessorCall`, `elabMethodCall`): the field's does, where it is
    used. -/
def accessorCtx (ctx : Ctx) : Ctx := { ctx with accessorCall := true }

/-- The indices and keys of a path into a field's value, each evaluated into
    a slot, in order, and the arguments the accessor is then called with
    (a struct's field by its name, a string). -/
def accessorKeys (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (steps : List PlaceStep) :
    EM (List Expr × List Local × List SExpr) := do
  let mut code : Array Expr := #[]
  let mut locals : List Local := []
  let mut keys : Array SExpr := #[]
  for step in steps do
    match step with
    | (kp, .inr k) =>
      let rk ← elabE { ctx with locals := locals ++ ctx.locals } k none
      let ks ← fresh rk.ty
      code := code.push (.assign ks rk.e)
      let kName := s!"$accessorKey{ks}"
      locals := { name := kName, slot := ks, ty := rk.ty, mutable := false } :: locals
      keys := keys.push (.ident kp kName)
    | step => keys := keys.push (accessorStepArg step)
  return (code.toList, locals, keys.toList)

/-- A read of a field with accessors, and of a path into its value: one call
    of the getter that takes the path (Book of Verse ch. 10, "Fields with
    Accessors"; DeepMutabilityForCustomClassVarAccessors.versetest:264-308),
    the receiver evaluated first, then the indices. -/
def elabAccessorRead (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (ctx : Ctx) (p : Pos) (place : AccessorPlace) (exp : Option Ty) : EM R := do
  if !place.overrides.isEmpty then eerr p "internal error: an overridden field read as one with accessors"
  checkMemberAccess ctx.types place.pos place.cls place.field.name
  let decides ← accessorDecides ctx p place "getter" place.field.getter place.steps.length
  let o ← elabE ctx place.recv none
  let slot ← fresh o.ty
  let name := s!"$accessorReceiver{slot}"
  let ctx' := { ctx with locals := { name, slot, ty := o.ty, mutable := false } :: ctx.locals }
  let (keyCode, keyLocals, keys) ← accessorKeys elabE ctx' place.steps
  let q := place.pos
  let ctx'' := accessorCtx { ctx' with locals := keyLocals ++ ctx'.locals }
  let r ← elabApp ctx'' q (.member q (.ident q name) place.field.getter) (accessorArg q :: keys) decides exp
  return ⟨(Expr.assign slot o.e :: keyCode).foldr Expr.seq r.e, r.ty⟩

/-- The call of an accessor `m` (with no path) on an object of class `d`
    held in slot `yd`, at `ty`. -/
def accessorOn (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R) (ctx : Ctx)
    (q : Pos) (d : String) (yd : Nat) (m : String) (args : List SExpr) (ty : Option Ty) : EM R := do
  let name := s!"$accessorObject{yd}"
  let ctx' := accessorCtx { ctx with locals := { name, slot := yd, ty := .struct d [], mutable := false } :: ctx.locals }
  elabApp ctx' q (.member q (.ident q name) m) (accessorArg q :: args) false ty

/-- A read of a field `place.cls` has with storage, which classes below give
    accessors: a test of the object's class, the getter of each such class,
    the field read (`elabMember`) for any other. -/
def elabOverriddenRead (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabMember : Ctx → Pos → R → String → EM R)
    (ctx : Ctx) (p : Pos) (place : AccessorPlace) (o : R) (x : Nat) : EM Expr := do
  let env := ctx.types
  let plain ← elabMember ctx p ⟨.local x, o.ty⟩ place.written
  let mut acc ← coerce p plain place.ty
  for (d, a) in place.overrides.reverse do
    let yd ← fresh (.struct d [])
    let r ← accessorOn elabApp ctx place.pos d yd a.getter [] (some place.ty)
    acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local x])) (← coerce p r place.ty) acc
  return acc

/-- `se`, a read that ends a path through a field with accessors, as its
    getter's call; `none` for any other expression. -/
def elabAccessorRead? (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabMember : Ctx → Pos → R → String → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (Option R) := do
  match se with
  | .member .. | .app _ _ [_] true | .ident .. => pure ()
  | _ => return none
  let (root, steps) := placeSteps se
  let places ← accessorPlaces elabE ctx root steps
  -- (the one nearest the end: a path into a value has one field with
  -- accessors, and one through an object is that object's)
  let some place := places.getLast? | return none
  let (taken, _) := accessorPath ctx.types place.ty place.steps
  if taken.length != place.steps.length then return none
  if !place.overrides.isEmpty then
    if !place.steps.isEmpty then
      eerr se.pos s!"{place.written} of {place.cls} is a field with accessors in classes below it: a path into its value through {place.cls} is not supported yet"
    checkMemberAccess ctx.types place.pos place.cls place.written
    let o ← elabE ctx place.recv none
    let x ← fresh o.ty
    let e ← elabOverriddenRead elabE elabApp elabMember ctx se.pos place o x
    let y ← fresh place.ty
    return some ⟨.seq (.assign x o.e) (.assign y e), place.ty⟩
  return some (← elabAccessorRead elabE elabApp ctx se.pos place exp)

/-- `set P (op)= V` where the place `P` reaches a field with accessors: the
    one nearest its root. When the place ends in the field's value, one call
    of the setter that takes the path's indices and the value (for `op=`,
    the getter's first: the receiver, the indices and `V` are evaluated
    first, in order, as a `set` evaluates its value before it reads the old
    one); when it goes on into an object, the getter's value, through which
    the rest is set. The value of the `set` is the value set. `none` for any
    other place. -/
def elabAccessorSet? (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabSet : Ctx → Pos → SExpr → Option String → SExpr → EM R)
    (elabMember : Ctx → Pos → R → String → EM R)
    (plainSet : Ctx → Pos → SExpr → Option String → SExpr → EM R)
    (ctx : Ctx) (p : Pos) (lhs : SExpr) (op : Option String) (rhs : SExpr) : EM (Option R) := do
  let (root, steps) := placeSteps lhs
  let places ← accessorPlaces elabE ctx root steps
  let some place := places.head? | return none
  let env := ctx.types
  if !place.overrides.isEmpty then
    -- (a field with storage, which classes below give accessors: a test of
    -- the object's class, each such class's setter, the field set for any
    -- other; the receiver, then the value, then for `op=` the old value)
    if !place.steps.isEmpty then
      eerr p s!"{place.written} of {place.cls} is a field with accessors in classes below it: setting a path into its value through {place.cls} is not supported yet"
    checkMemberAccess env place.pos place.cls place.written (write := true)
    let q := place.pos
    let o ← elabE ctx place.recv none
    let x ← fresh o.ty
    let oName := s!"$accessorReceiver{x}"
    let ctx1 := { ctx with locals := { name := oName, slot := x, ty := o.ty, mutable := false } :: ctx.locals }
    let rv ← elabE ctx1 rhs (some place.ty)
    let mut code : Array Expr := #[.assign x o.e]
    let newValue ← match op with
      | none => coerce rhs.pos rv place.ty
      | some opn =>
        let vs ← fresh rv.ty
        code := code.push (.assign vs rv.e)
        let old ← elabOverriddenRead elabE elabApp elabMember ctx1 p place o x
        let olds ← fresh place.ty
        code := code.push (.assign olds old)
        let ctx2 := { ctx1 with locals := { name := s!"$accessorOld{olds}", slot := olds, ty := place.ty, mutable := false } ::
                                         { name := s!"$accessorValue{vs}", slot := vs, ty := rv.ty, mutable := false } :: ctx1.locals }
        let r ← elabE ctx2 (.bin p opn (.ident q s!"$accessorOld{olds}") (.ident q s!"$accessorValue{vs}")) (some place.ty)
        coerce p r place.ty
    let ns ← fresh place.ty
    code := code.push (.assign ns newValue)
    let nName := s!"$accessorNew{ns}"
    let ctx3 := { ctx1 with locals := { name := nName, slot := ns, ty := place.ty, mutable := false } :: ctx1.locals }
    let plain ← plainSet ctx3 p (.member q (.ident q oName) place.written) none (.ident q nName)
    let mut acc : Expr := .seq plain.e (.local ns)
    for (d, a) in place.overrides.reverse do
      let yd ← fresh (.struct d [])
      let r ← accessorOn elabApp ctx3 q d yd a.setter [.ident q nName] none
      acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local x])) (.seq r.e (.local ns)) acc
    let y ← fresh place.ty
    code := code.push (.assign y acc)
    return some ⟨code.toList.foldr Expr.seq (.local y), place.ty⟩
  let (taken, valueTy) := accessorPath env place.ty place.steps
  if taken.length != place.steps.length then
    -- (into an object: its value through the getter, then the rest set)
    let rest := place.steps.drop taken.length
    let .struct oc _ := valueTy
      | eerr p s!"{place.written} is a field with accessors: this place goes on from its value, {valueTy.show}, where a set cannot"
    if !env.classes.contains oc then
      eerr p s!"{place.written} is a field with accessors: this place goes on from its value, {valueTy.show}, where a set cannot"
    let r ← elabAccessorRead elabE elabApp ctx p { place with steps := taken } none
    let slot ← fresh r.ty
    let name := s!"$accessorObject{slot}"
    let ctx' := { ctx with locals := { name, slot, ty := r.ty, mutable := false } :: ctx.locals }
    let s ← elabSet ctx' p (placeOf (.ident p name) rest) op rhs
    return some ⟨.seq (.assign slot r.e) s.e, s.ty⟩
  checkMemberAccess env place.pos place.cls place.field.name (write := true)
  let n := place.steps.length
  let setDecides ← accessorDecides ctx p place "setter" place.field.setter (n + 1)
  let getDecides ← if op.isSome then accessorDecides ctx p place "getter" place.field.getter n else pure false
  let q := place.pos
  -- the receiver, then the indices, then the value, each in a slot
  let mut code : Array Expr := #[]
  let mut locals := ctx.locals
  let o ← elabE ctx place.recv none
  let os ← fresh o.ty
  code := code.push (.assign os o.e)
  let oName := s!"$accessorReceiver{os}"
  locals := { name := oName, slot := os, ty := o.ty, mutable := false } :: locals
  let mut keys : Array SExpr := #[]
  for step in place.steps do
    match step with
    | (_, .inr k) =>
      let rk ← elabE { ctx with locals } k none
      let ks ← fresh rk.ty
      code := code.push (.assign ks rk.e)
      let kName := s!"$accessorKey{ks}"
      locals := { name := kName, slot := ks, ty := rk.ty, mutable := false } :: locals
      keys := keys.push (.ident q kName)
    | step => keys := keys.push (accessorStepArg step)
  let ctx1 := { ctx with locals }
  let rv ← elabE ctx1 rhs (some valueTy)
  let newValue ← match op with
    | none => coerce rhs.pos rv valueTy
    | some o =>
      -- (the old value through the getter, after the value)
      let vs ← fresh rv.ty
      code := code.push (.assign vs rv.e)
      let old ← elabApp (accessorCtx ctx1) q (.member q (.ident q oName) place.field.getter)
        (accessorArg q :: keys.toList) getDecides (some valueTy)
      let olds ← fresh old.ty
      code := code.push (.assign olds old.e)
      let ctx2 := { ctx1 with locals := { name := s!"$accessorOld{olds}", slot := olds, ty := old.ty, mutable := false } ::
                                       { name := s!"$accessorValue{vs}", slot := vs, ty := rv.ty, mutable := false } :: ctx1.locals }
      let r ← elabE ctx2 (.bin p o (.ident q s!"$accessorOld{olds}") (.ident q s!"$accessorValue{vs}")) (some valueTy)
      coerce p r valueTy
  let ns ← fresh valueTy
  code := code.push (.assign ns newValue)
  let ctx3 := { ctx1 with locals := { name := s!"$accessorNew{ns}", slot := ns, ty := valueTy, mutable := false } :: ctx1.locals }
  let call ← elabApp (accessorCtx ctx3) q (.member q (.ident q oName) place.field.setter)
    (accessorArg q :: keys.toList ++ [.ident q s!"$accessorNew{ns}"]) setDecides none
  code := code.push call.e
  return some ⟨code.toList.foldr Expr.seq (.local ns), valueTy⟩

/-- The values of a construction of `name` that gives fields with
    accessors (`gives`), each into a slot, in the order the fields are
    declared, as a construction evaluates its fields: those with storage
    (`storedValue`: the value given, or the default) and those with accessors
    given, at their types. Gives the code, the slots of the stored ones (the
    object's fields) and those of the others, for their setters. -/
def accessorValues (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (name : String) (tas : List Ty)
    (fs : List (String × Ty × Option SExpr)) (storedValue : String → Ty → Option SExpr → EM Expr)
    (gives : List (String × SExpr)) : EM (List Expr × List Expr × List (AccessorField × Nat × Ty × Pos)) := do
  let env := ctx.types
  let declIx (a : AccessorField) : Nat :=
    (env.accessors.findIdx? fun b => b.owner == a.owner && b.name == a.name).getD 0
  let accs := (gives.filterMap fun (f, rhs) => (env.accessorOf? name tas f).map fun (a, t) => (a, t, rhs)).toArray
    |>.qsort (fun x y => declIx x.1 < declIx y.1) |>.toList
  let names := fs.map (·.1)
  let anchored (a : AccessorField) : Bool := a.prev.any names.contains || a.next.any names.contains
  let mut pre : Array Expr := #[]
  let mut stored : Array Expr := #[]
  let mut vals : Array (AccessorField × Nat × Ty × Pos) := #[]
  let mut order : Array (Sum (String × Ty × Option SExpr) (AccessorField × Ty × SExpr)) := #[]
  for field@(f, _, _) in fs do
    for x@(a, _, _) in accs do
      if !(a.prev.any names.contains) && a.next == some f then order := order.push (.inr x)
    order := order.push (.inl field)
    for x@(a, _, _) in accs do
      if a.prev == some f then order := order.push (.inr x)
  for x@(a, _, _) in accs do
    if !anchored a then order := order.push (.inr x)
  for item in order do
    match item with
    | .inl (f, t, dflt) =>
      let e ← storedValue f t dflt
      let s ← fresh t
      pre := pre.push (.assign s e)
      stored := stored.push (.local s)
    | .inr (a, t, rhs) =>
      let e ← coerce rhs.pos (← elabE ctx rhs (some t)) t
      let s ← fresh t
      pre := pre.push (.assign s e)
      vals := vals.push (a, s, t, rhs.pos)
  return (pre.toList, stored.toList, vals.toList)

/-- The calls of the setters of the fields with accessors a construction
    gives, their values in slots (`accessorValues`), on the new object in
    slot `x`: they run once its fields have their values, before its
    `block:` clauses (Book of Verse tests, CustomClassVarAccessors.versetest
    661-681: `set X = 10` in a `block:` is what stays; 565-589: a setter sees
    the other fields set). -/
def accessorSetters (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (ctx : Ctx) (ty : Ty) (vals : List (AccessorField × Nat × Ty × Pos)) (x : Nat) : EM (List Expr) := do
  let self := s!"$new{x}"
  let ctx0 := accessorCtx { ctx with locals := { name := self, slot := x, ty, mutable := false } :: ctx.locals }
  -- (each at the place of its value, `X := V`)
  vals.mapM fun (a, vs, t, q) => do
    let vName := s!"$accessorValue{vs}"
    let ctx' := { ctx0 with locals := { name := vName, slot := vs, ty := t, mutable := false } :: ctx0.locals }
    return (← elabApp ctx' q (.member q (.ident q self) a.setter) [accessorArg q, .ident q vName] false none).e

end OpenVerse.Front
