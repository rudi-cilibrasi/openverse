/-
  OpenVerse — the variance of parametric classes and interfaces (Book of
  Verse ch. 10, "Instantiation and Identity"; docs/research/variance.md).

  Two variances, of two languages:
  * the Book's (`SVar`, `TyEnv.bookVariances`): how each type parameter of a
    class or interface is used in its member signatures, inherited ones
    included: fields that are no `var` and methods' results covariantly,
    methods' parameters contravariantly, `var` fields invariantly, a type
    argument of another class or interface by that one's variance there, a
    function type's parameters contravariantly. The most permissive variance
    consistent with all uses, as a fixpoint from bivariant (a parameter used
    only at a bivariant position of the class's own type is bivariant).
  * Verse Core's (`Sigs.inferVariances`), over each concrete class's field
    table, its pins and the fields written through a reference: what makes a
    reference at other type arguments than its object's sound (the checker
    checks it, `Sigs.checkVarOK`).
  A conversion by variance needs both (`refUp`): the Book's, and Verse
  Core's subtyping of the two references, as the value is not converted.
-/
import OpenVerse.Front.Types

namespace OpenVerse.Front

/-- How the type parameter `p` is used in `t`, given the Book's variances `V`
    of the classes and interfaces it mentions. -/
partial def Ty.polOf (env : TyEnv) (V : String → List SVar) (p : String) : Ty → SVar
  | .param n _ => if n == p then .co else .bi
  | .arr t | .opt t => t.polOf env V p
  | .tup ts => ts.foldl (fun acc t => acc.join (t.polOf env V p)) .bi
  -- (maps are covariant in their keys and values, Book of Verse ch. 3)
  | .map k v | .weakMap k v => (k.polOf env V p).join (v.polOf env V p)
  | .struct n args =>
    match FnValues.parse n with
    -- (a function type, a hidden interface's instance whose type arguments
    -- are its parameters', then its result's, #210: parameters contravariant,
    -- the result covariant, Book of Verse ch. 6)
    | some _ =>
      args.zipIdx.foldl (fun acc (a, j) =>
        acc.join (if j + 1 == args.length then a.polOf env V p else (a.polOf env V p).flip)) .bi
    | none =>
      if env.classes.contains n then
        args.zipIdx.foldl (fun acc (a, j) => acc.join (((V n)[j]?.getD .inv).compose (a.polOf env V p))) .bi
      -- (a struct, a type value: its type arguments as they are)
      else args.foldl (fun acc a => acc.join (SVar.inv.compose (a.polOf env V p))) .bi
  | _ => .bi

/-- The classes and interfaces `n` lists as parents, each with the type
    arguments it gives it, over its own type parameters. -/
def TyEnv.parentsWithArgs (env : TyEnv) (n : String) : List (String × List Ty) :=
  (env.info n).parent.toList.map (fun q => (q, (env.pargs.lookup n).getD [])) ++
    (env.info n).ifaces.map fun i => (i, (env.iargs.lookup (n, i)).getD [])

/-- **The Book's variances** of the classes and interfaces, given each one's
    methods (by class or interface: each method's parameter types, its
    receiver left out, and its result type, over the type's parameters):
    the use of each type parameter in the fields, the methods and the parents
    at the type arguments it gives them, from bivariant up to a fixpoint. -/
def TyEnv.bookVariances (env : TyEnv) (methods : List (String × List (String × List Ty × Ty))) :
    List (String × List SVar) := Id.run do
  let params (n : String) : List String := ((env.sparams.lookup n).getD []).map (·.1)
  -- (function types' shapes are taken by `Ty.polOf` as the Book has
  -- function types, and converted by adapters, #214)
  let names := env.classes.filter fun n => !(params n).isEmpty && (FnValues.parse n).isNone
  let total := names.foldl (fun acc n => acc + (params n).length) 0
  let mut V : Std.HashMap String (List SVar) :=
    names.foldl (fun m n => m.insert n ((params n).map fun _ => .bi)) {}
  for _ in [0:2 * total + 2] do
    let get (n : String) : List SVar := V[n]?.getD ((params n).map fun _ => .inv)
    let mut changed := false
    let mut next := V
    for n in names do
      let uses := (params n).map fun p => Id.run do
        let mut u := SVar.bi
        for (f, t, _) in env.fields n do
          let x := t.polOf env get p
          u := u.join (if env.isVarField n f && x != .bi then .inv else x)
        for (_, pts, r) in (methods.lookup n).getD [] do
          for pt in pts do u := u.join (pt.polOf env get p).flip
          u := u.join (r.polOf env get p)
        for (q, qargs) in env.parentsWithArgs n do
          u := u.join ((Ty.struct q qargs).polOf env get p)
        return u
      if uses != get n then
        next := next.insert n uses
        changed := true
    V := next
    if !changed then break
  return names.map fun n => (n, V[n]?.getD [])

/-- Verse Core's class table: each class's field types over its Verse Core
    type arguments, as the certificate gives it (`Sigs.classes`). -/
def TyEnv.coreClassTable (env : TyEnv) : List (List VTy) :=
  env.classes.map fun d =>
    if env.isRefClass d then (env.fields d).map fun (f, t, _) =>
      (env.coreFieldTy d f).getD (t.toVTy { env with tvars := env.coreVars d })
    else []

/-- Verse Core's pins, as the certificate gives them (`Sigs.pins`). -/
def TyEnv.corePinTable (env : TyEnv) : List (List (Option VTy)) :=
  env.classes.map fun d => if env.isRefClass d then env.lowerPins (env.dispatchPins d) else []

/-- **Verse Core's variances** (`Sigs.variances`): the most permissive the
    class table and the pins allow (`Sigs.inferVariances`), each type
    argument that a field written through a reference mentions (a `var`
    field, or one with an accessor pair, #157) or that a view of an
    interface above the class mentions (#351, whose references relate type
    arguments by equations) invariant. -/
def TyEnv.coreVariancesOf (env : TyEnv) : List (List Variance) :=
  let table := env.coreClassTable
  let S : Sigs := { fns := [], classes := table, pins := env.corePinTable }
  let classes := env.classes.toArray
  let arity (t : Nat) : Nat := match classes[t]? with
    | some d => (env.coreVars d).length
    | none => 0
  -- (the views of the interfaces above each class that are referred to
  -- through views, over its Verse Core type arguments)
  let views (d : String) : List VTy :=
    (env.viewed.filter fun n => n != d && env.isSub d n).flatMap fun n =>
      let X := (List.range (env.coreVars d).length).map fun j => Ty.param (pinArg j) false
      (env.viewOf n d X).map (Ty.toVTy { env with tvars := X.zipIdx.map fun (x, j) => (pinArg j, x) })
  -- (a field written through a reference: a `var` field or one with an
  -- accessor pair of the class or of one above it, which a placeholder
  -- below it has too, #157)
  let written (d f : String) : Bool :=
    (env.varFields ++ env.fieldAcc).any fun (c, g) => g == f && (c == d || env.isSub d c)
  let fixed (t i : Nat) : Bool := match classes[t]? with
    | some d =>
      let fs := (table[t]?).getD []
      ((env.fields d).zip fs).any (fun ((f, _, _), ft) => written d f && ft.hasVar i) ||
        (views d).any (·.hasVar i)
    | none => true
  S.inferVariances arity fixed

end OpenVerse.Front

namespace OpenVerse.Front

/-- `x` with its indefinite article. -/
def withAn (x : String) : String :=
  if x.startsWith "a" || x.startsWith "e" || x.startsWith "i" || x.startsWith "o" || x.startsWith "u" then s!"an {x}"
  else s!"a {x}"

/-- The members of class or interface `n` (its own fields and methods, then
    its parents) that use its type parameter `p`, each with how. -/
def TyEnv.varianceUses (env : TyEnv) (n p : String) : List (String × SVar) :=
  let V := env.varianceOf
  let fields := (env.fields n).filterMap fun (f, t, _) =>
    let x := t.polOf env V p
    if x == .bi then none
    else some (if env.isVarField n f then s!"var {f}" else f, if env.isVarField n f then .inv else x)
  let methods := ((env.memberSigs.lookup n).getD []).filterMap fun (m, pts, r) =>
    let x := (pts.foldl (fun (acc : SVar) t => acc.join (t.polOf env V p).flip) SVar.bi).join (r.polOf env V p)
    if x == .bi then none else some (s!"{m}'s signature", x)
  let parents := (env.parentsWithArgs n).filterMap fun (q, qargs) =>
    let x := (Ty.struct q qargs).polOf env V p
    if x == .bi then none else some (s!"what {q} declares", x)
  fields ++ methods ++ parents

/-- Why `a(as)`, a class type, is no `b(bs)` above it when only type
    arguments differ: the Book's variance of the class or interface above
    (ch. 10, "Instantiation and Identity"), or, where the Book has it a
    subtype, what Verse Core needs that it does not have (a reference is
    typed by its object's own class: docs/research/variance.md). -/
def TyEnv.varianceWhy (env : TyEnv) (a b : Ty) : Option String := do
  let .struct S as := a | none
  let .struct T bs := b | none
  if !env.classes.contains S || !env.classes.contains T || !env.isSub S T then none
  if (FnValues.parse T).isSome then none
  let us := env.upArgs S as T
  if us == bs || us.length != bs.length then none
  let ps := ((env.sparams.lookup T).getD []).map (·.1)
  let vs := env.varianceOf T
  let book : Option String := ((ps.zip vs).zip (us.zip bs)).findSome? fun ((p, v), (u, w)) =>
    let fits := match v with
      | .inv => u == w
      | .co => env.argFits u w
      | .contra => env.argFits w u
      | .bi => true
    if fits then none else
    let uses := env.varianceUses T p
    let shown := ", ".intercalate (uses.map fun (m, x) => s!"{m} ({x.show})")
    let usedIn := if uses.isEmpty then "" else s!": {p} is used in {shown}"
    -- (a type argument that would have to be converted: a value of it is
    -- one of the other in Verse, but not as it is)
    let conv (x y : Ty) : Option String :=
      if y == .any && x != .any then some s!"an any holds no value in openverse"
      else if x == .int && y == .rational ||
          y == .dyn && x != .dyn && x.comparable env && !x.boxId env then
        some s!"a value of {x.show} becomes one of {y.show} only converted"
      else none
    let notAsIs (x y : Ty) (c : String) : String :=
      s!"{withAn x.show} is {withAn y.show}, but not as it is: {c}, which {withAn T} holding it cannot be, so {a.show} is no {b.show} in openverse"
    match v with
    | .inv => some s!"{T} is invariant in {p}{usedIn}, so {a.show} is no {b.show} (Book of Verse ch. 10, \"Invariant\")"
    | .co => match conv u w with
      | some c => some s!"{T} is covariant in {p}{usedIn}; {notAsIs u w c} (Book of Verse ch. 10, \"Covariant\")"
      | none => some s!"{T} is covariant in {p}{usedIn}, so {T}({u.show}) is {withAn s!"{T}({w.show})"} only when {u.show} is {withAn w.show} (Book of Verse ch. 10, \"Covariant\")"
    | .contra => match conv w u with
      | some c => some s!"{T} is contravariant in {p}{usedIn}; {notAsIs w u c} (Book of Verse ch. 10, \"Contravariant\")"
      | none => some s!"{T} is contravariant in {p}{usedIn}, so {T}({u.show}) is {withAn s!"{T}({w.show})"} only when {w.show} is {withAn u.show} (Book of Verse ch. 10, \"Contravariant\")"
    | .bi => none
  match book with
  | some m => some m
  | none =>
    -- the Book has it a subtype: what Verse Core refuses
    match a.toVTy env, b.toVTy env with
    | .ref ts xs, .ref _ ys =>
      let V := env.coreVar
      let why := ts.findSome? fun tag => do
        let d ← env.classes[tag]?
        let j ← ((xs.zip ys).zipIdx.find? fun ((x, y), j) =>
          match V tag j with
          | .inv => x != y
          | .co => !x.sub V y
          | .bi => false).map (·.2)
        let pins := env.lowerPins (env.dispatchPins d)
        let pinned := pins.zipIdx.any fun (o, i) => match o with
          | some c => i == j || c.hasVar j
          | none => false
        let table := env.coreClassTable
        let fs := (table[tag]?).getD []
        let written (f : String) : Bool :=
          (env.varFields ++ env.fieldAcc).any fun (c, g) => g == f && (c == d || env.isSub d c)
        -- (invariant there: a write, an invariant use; covariant: a use)
        let fieldWhy := if V tag j == .inv then
            ((env.fields d).zip fs).findSome? (fun ((f, _, _), ft) =>
              if written f && ft.hasVar j then some s!"writes its field {f} at it" else none) |>.orElse fun _ =>
            ((env.fields d).zip fs).findSome? fun ((f, _, _), ft) =>
              if ft.useOf V j == .inv then some s!"uses it invariantly in its field {f}" else none
          else ((env.fields d).zip fs).findSome? fun ((f, _, _), ft) =>
            if ft.useOf V j != .bi then some s!"holds it in its field {f}" else none
        let reason := if pinned then s!"fixes it (it overrides a method {T} declares, or a cast refines to it)"
          else fieldWhy.getD "refers to it through an interface's view"
        some (d, reason)
      match why with
      | some (d, reason) =>
        some s!"{a.show} is {withAn b.show} by {T}'s variance (Book of Verse ch. 10), but not in openverse yet: {d}, a class below {T}, {reason}, and Verse Core types a reference by its object's own class (docs/research/variance.md)"
      | none => none
    | _, .vref .. =>
      some s!"{a.show} is {withAn b.show} by {T}'s variance (Book of Verse ch. 10), but not in openverse yet: {T} is referred to through views (#351), which relate type arguments exactly"
    | _, _ => none

end OpenVerse.Front
