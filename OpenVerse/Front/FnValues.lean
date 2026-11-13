import OpenVerse.Front.SubtypeSyntax
import OpenVerse.Front.Choice

/-!
Function values (#210), defunctionalised before elaboration.

A function type `type{_(:t₁, …, :tₙ)<effects>:r}` (or `t₁->r`) is an
instance of a hidden generic interface, one per arity and effects (its
*shape*): `$fn2:decides(t₁, t₂, r)`, with the abstract method
`$call:decides(X₀:t₁, X₁:t₂)<decides>:r`. A shape with fewer effects
extends one with more, at the same type arguments, so a function type with
fewer effects is a subtype of one with more (Book of Verse, functions).

A top-level function `F` used as a value is an object of a hidden class
`F$fn` that implements every shape of the program it fits, at `F`'s own
parameter and result types: its `$call…` calls `F`. Such a class fixes the
shapes' type arguments, so code generic over a function type calls it
under the refinement of #142, like any class that fixes an interface's.
Parameter and result types are matched exactly: `F(X:rational)` does not
fit `type{_(:int):rational}`.

Named parameters (#503) are part of a shape, after the positional ones and
in the order of their names: `type{_(:int, ?B:int):int}` is `$fn2?B(int,
int, int)`, whose method `$call?B(X₀:a₀, ?B:a₁)` a call names `B` of. A
function fits every shape with its positional parameters, names among its
own and every name it requires (`Shape.within`): its value class's method
for each passes exactly the shape's arguments, so the function's own
defaults fill in the rest at the call, in its scope and order. A named
parameter a caller of the type may omit (`?C:int = …`) makes an open shape,
`$fn3?B?C=`: one with no method, below the closed shapes of the program
that give some of its optional parameters (a call needing one the program
lacks asks for it, `fnValueCall`).

The elaborator resolves a function type to its shape (`resolveTy`), turns
a function named as a value into its class's object (`.ident`), and a call
of a value of a shape's type into a call of its `$call…` method
(`elabIndexLike`).
-/

namespace OpenVerse.Front

/-- The heap effects of #35. -/
def heapFx : List String := ["allocates", "reads", "writes"]

/-- The heap effects a function's specifiers allow: all of them by default
    and with `<transacts>`, none with `<computes>`, those named by
    `<allocates>`, `<reads>`, `<writes>`. -/
def allowedFx (effs : List String) : List String :=
  if effs.contains "transacts" then heapFx
  else
    let named := heapFx.filter effs.contains
    if !named.isEmpty then named
    else if effs.contains "computes" then []
    else heapFx

namespace FnValues

/-- A function type's parameters and effects: the hidden interface it is an
    instance of. Its named parameters come last, in the order of their
    names, as a call names them in any order (#503). -/
structure Shape where
  /-- All its parameters, positional and named. -/
  arity : Nat
  decides : Bool := false
  suspends : Bool := false
  /-- The heap effects it allows, in `heapFx`'s order. -/
  fx : List String := heapFx
  /-- Its named parameters' names, sorted: the last `named.length`. -/
  named : List String := []
  /-- Those of `named` a caller may omit (`?N:t = …` in the type). -/
  optional : List String := []
  deriving BEq, Repr, Inhabited

def shapeOf (arity : Nat) (effs : List String) (named : List String := []) (optional : List String := []) :
    Shape :=
  { arity, decides := effs.contains "decides", suspends := effs.contains "suspends", fx := allowedFx effs,
    named, optional }

/-- How many positional parameters a shape has. -/
def Shape.positional (s : Shape) : Nat := s.arity - s.named.length

/-- The shape with `s`'s effects of the parameters `ps` (`some (name,
    optional)` for a named one), and the permutation that puts the named
    ones in order: the index in `ps` of each of the shape's parameters. -/
def Shape.withParams (s : Shape) (ps : List (Option (String × Bool))) : Shape × List Nat :=
  let pos := (ps.zipIdx.filter (·.1.isNone)).map (·.2)
  let named := (ps.zipIdx.filterMap fun (q, i) => q.map fun (n, o) => (n, o, i)).mergeSort
    fun (a, _, _) (b, _, _) => a ≤ b
  let optional := named.filterMap fun (n, o, _) => if o then some n else none
  ({ s with arity := ps.length, named := named.map (·.1), optional }, pos ++ named.map (·.2.2))

def shapeOfParams (ps : List (Option (String × Bool))) (effs : List String) : Shape × List Nat :=
  (shapeOf 0 effs).withParams ps

/-- The effect specifiers that give a shape's effects. -/
def Shape.effs (s : Shape) : List String :=
  (if s.decides then ["decides"] else []) ++ (if s.suspends then ["suspends"] else []) ++
  (if s.fx == heapFx then [] else if s.fx.isEmpty then ["computes"] else s.fx)

/-- The effects part of a shape's names: `:decides:reads`, say. -/
def Shape.tag (s : Shape) : String := String.join (s.effs.map (":" ++ ·))

/-- The named parameters part of a shape's names: `?A?B=`, `=` marking one
    a caller may omit. -/
def Shape.namesTag (s : Shape) : String :=
  String.join (s.named.map fun n => "?" ++ n ++ if s.optional.contains n then "=" else "")

/-- The hidden interface of a shape. -/
def Shape.name (s : Shape) : String := s!"$fn{s.arity}{s.namesTag}{s.tag}"

/-- A shape whose every parameter a call gives. Only such a shape has a
    method: a shape with optional ones is the intersection of those that
    give each set of them (`Shape.supplying`). -/
def Shape.closed (s : Shape) : Bool := s.optional.isEmpty

/-- The hidden interface's method, of a closed shape. -/
def Shape.call (s : Shape) : String := s!"$call{s.namesTag}{s.tag}"

/-- The closed shape a call of shape `s` that names `names` is a call of:
    `s` without the optional parameters it omits. -/
def Shape.supplying (s : Shape) (names : List String) : Shape :=
  let dropped := s.optional.filter (!names.contains ·)
  { s with arity := s.arity - dropped.length, named := s.named.filter (!dropped.contains ·), optional := [] }

/-- The shape interface named `n`, and the effect specifiers its name
    writes. -/
def parseWritten (n : String) : Option (Shape × List String) :=
  if !n.startsWith "$fn" then none else
  match (n.drop 3).toString.splitOn ":" with
  | head :: effs =>
    match head.splitOn "?" with
    | a :: names =>
      a.toNat?.map fun k =>
        (shapeOf k effs (names.map (·.replace "=" "")) (names.filterMap fun n =>
          if n.endsWith "=" then some (n.dropEnd 1).toString else none), effs)
    | [] => none
  | [] => none

/-- The shape interface named `n`. -/
def parse (n : String) : Option Shape := (parseWritten n).map (·.1)

/-- Whether `n` is a shape's interface; its arity and effects, as named. -/
def parseName (n : String) : Option (Nat × List String) :=
  (parseWritten n).map fun (s, effs) => (s.arity, effs)

/-- A function type as Verse writes it: `type{_(:int, ?B:string)<decides>:float}`,
    an optional parameter `?C:int = …` (the type has no default). -/
def Shape.show (s : Shape) (ps : List String) (r : String) (effs : List String := s.effs) : String :=
  let named := s.named.zip (ps.drop s.positional) |>.map fun (n, t) =>
    s!"?{n}:{t}" ++ if s.optional.contains n then " = …" else ""
  "type{_(" ++ ", ".intercalate ((ps.take s.positional).map (":" ++ ·) ++ named) ++ ")" ++
    String.join (effs.map fun e => s!"<{e}>") ++ ":" ++ r ++ "}"

/-- An error message with the hidden names read as Verse: `F$fn.$call…`
    is `F` called as a value, another `$call…` a function value, a shape's
    interface a function type. -/
def pretty (msg : String) : String :=
  let delim (c : Char) : Bool := c == ' ' || c == ',' || c == ';' || c == '\'' || c == '(' || c == ')' ||
    c == '\n'
  let word (w : String) : String :=
    if !(w.splitOn "$call").tail.isEmpty then
      match w.splitOn "$fn.$call" with
      | f :: _ :: _ => s!"{f.replace "$" "."} (called as a function value)"
      | _ => "a function value"
    else if w.startsWith "$fn" then "a function type"
    -- (the prelude's `subscribable_event()`, #220)
    else if w == "$subev0" then "subscribable_event()"
    else if ["$event", "$sticky_event", "$task", "$subscribable_event", "$cancelable"].contains
        ((w.splitOn ".").headD "") then (w.drop 1).toString
    else w
  Id.run do
    let mut out := ""
    let mut cur := ""
    for c in (msg.replace "class $fn" "$fn").toList do
      if delim c then
        out := out ++ word cur ++ c.toString
        cur := ""
      else cur := cur.push c
    return out ++ word cur

/-- A function of shape `s` is one of shape `t` too: its effects are among
    `t`'s, it has the positional parameters and the names `t` has, and
    a call of `t` may omit only what a call of `s` may: one of `t`'s
    optional parameters, or one `t` lacks (Book of Verse ch. 6, "a function
    with default parameters is a subtype of the same function without
    those parameters", #503). -/
def Shape.within (s t : Shape) : Bool :=
  s.positional == t.positional && t.named.all s.named.contains &&
    s.named.all (fun n => t.named.contains n || s.optional.contains n) && t.optional.all s.optional.contains &&
    (!s.decides || t.decides) && (!s.suspends || t.suspends) && s.fx.all t.fx.contains

/-- Of the arguments `args` of shape `s` (its parameters', then its
    result's), those of a shape `t` it is `within`. -/
def Shape.select (s t : Shape) (args : List α) : List α :=
  args.take s.positional ++ t.named.filterMap (fun n => (s.named.idxOf? n).bind (args[s.positional + ·]?)) ++
    args.drop s.arity

/-- A function type's shape, its parameters' types in the shape's order
    (the named ones by name), and its result type. -/
def fnTyShape (ps : List STy) (es : List String) (r : STy) : Shape × List STy × STy :=
  let (s, order) := shapeOfParams (ps.map (·.asNamedParam?.map fun (n, o, _) => (n, o))) es
  (s, order.filterMap fun i => ps[i]?.map fun t => (t.asNamedParam?.map (·.2.2)).getD t, r)

/-- The function type of shape `s` at the types `ts` (its parameters', in the
    shape's order) and `r`, with effect specifiers `effs`: `fnTyShape`'s
    inverse. -/
def Shape.toSTy (s : Shape) (ts : List STy) (r : STy) (effs : List String := s.effs) : STy :=
  .fn (ts.take s.positional ++ (s.named.zip (ts.drop s.positional)).map fun (n, t) =>
    STy.namedParam n (s.optional.contains n) t) effs r

partial def _root_.OpenVerse.Front.STy.fnShapes : STy → List Shape
  | .name _ => []
  | .arr t | .opt t => t.fnShapes
  | .tup ts | .app _ ts => ts.flatMap STy.fnShapes
  | .map a b => a.fnShapes ++ b.fnShapes
  | .fn ps es r =>
    -- (a type both <decides> and <suspends>, or naming a parameter twice,
    -- has none: `resolveTy` refuses it)
    let s := (fnTyShape ps es r).1
    (if s.decides && s.suspends || s.named.eraseDups.length != s.named.length then [] else [s]) ++
      ps.flatMap STy.fnShapes ++ r.fnShapes

/-- The type names an expression mentions: in its types and constructions. -/
partial def _root_.OpenVerse.Front.SExpr.tyNames : SExpr → List String
  | .decl _ _ t _ e => (t.map STy.allNames).getD [] ++ e.tyNames
  | .construct _ n ts args => n :: ts.flatMap STy.allNames ++ args.flatMap SExpr.tyNames
  -- (type definitions, which `children` leaves out)
  | .structDef _ tps _ fs =>
    tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.allNames) ++
      fs.flatMap fun (_, t, d, _) => t.allNames ++ (d.map SExpr.tyNames).getD []
  | .refineDef _ _ t cs => t.allNames ++ cs.flatMap SExpr.tyNames
  | e => e.children.flatMap SExpr.tyNames

/-- Whether a definition mentions the type `n`. -/
partial def _root_.OpenVerse.Front.STop.usesType (n : String) : STop → Bool
  | .fn _ _ ps tps _ r body =>
    (tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.allNames) ++
      ps.flatMap (·.ty.allNames) ++ r.allNames ++ body.tyNames).contains n
  | .const _ _ t e => ((t.map STy.allNames).getD [] ++ e.tyNames).contains n
  | .classDef _ _ tps _ parents _ fields _ methods =>
    (tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.allNames) ++ parents.flatMap STy.allNames ++
      fields.flatMap (fun (_, t, d, _) => t.allNames ++ (d.map SExpr.tyNames).getD [])).contains n ||
      methods.any (STop.usesType n)

mutual
/-- The function types written in an expression, and the names it uses as
    values (not as the head of a call): `.M` for a member `X.M`. -/
partial def _root_.OpenVerse.Front.SExpr.scan : SExpr → List Shape × List String
  | .ident _ n => ([], [n])
  | .app _ (.ident _ _) args _ => scanL args
  | .app _ (.member _ e _) args _ => scanL (e :: args)
  | .app _ f args _ => scanL (f :: args)
  | .member _ e m =>
    let (s, n) := e.scan
    (s, n ++ ["." ++ m])
  | .query _ e | .neg _ e | .notE _ e | .optionLit _ e | .logicLit _ e | .loop _ e
  | .gen _ _ _ e => e.scan
  | .forE _ cs b =>
    -- (a generator's names are bound there: `for (Double : Xs)` means them)
    let bound := cs.flatMap fun | .gen _ x i _ => x :: i.toList | _ => []
    let (s, n) := scanL (cs ++ [b])
    (s, n.filter (!bound.contains ·))
  | .decl _ _ t _ e =>
    let (s, n) := e.scan
    ((t.map STy.fnShapes).getD [] ++ s, n)
  | .structDef _ tps _ fs =>
    let (s, n) := scanL (fs.filterMap (·.2.2.1))
    (tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.fnShapes) ++ fs.flatMap (·.2.1.fnShapes) ++ s, n)
  | .refineDef _ _ t cs =>
    let (s, n) := scanL cs
    (t.fnShapes ++ s, n)
  | .construct _ _ ts args =>
    let (s, n) := scanL args
    (ts.flatMap STy.fnShapes ++ s, n)
  | e => scanL e.children
partial def scanL (es : List SExpr) : List Shape × List String :=
  es.foldl (fun (s, n) e => let (s', n') := e.scan; (s ++ s', n ++ n')) ([], [])
end

partial def _root_.OpenVerse.Front.SParam.scan (q : SParam) : List Shape × List String :=
  let (s, n) := scanL q.default.toList
  (q.ty.fnShapes ++ s, n)

/-- The function types a definition writes, and the names it uses as
    values, but for its parameters' names and `bound` (the fields of the
    classes, in a method: a parameter or a field of that name is meant). A
    name in `meths` (a method of the class, in its methods) is `Self`'s
    method, `.M`. -/
partial def _root_.OpenVerse.Front.STop.scan (bound : List String := []) (meths : List String := []) :
    STop → List Shape × List String
  | .fn _ _ ps tps _ r body =>
    let (s, n) := scanL [body]
    let pss := ps.map SParam.scan
    let mine := ps.map (·.name) ++ bound
    (tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.fnShapes) ++
      r.fnShapes ++ pss.flatMap (·.1) ++ s, (pss.flatMap (·.2) ++ n).filter (!mine.contains ·))
  | .const _ _ t e =>
    let (s, n) := e.scan
    ((t.map STy.fnShapes).getD [] ++ s, n)
  | .classDef _ _ tps _ parents _ fields _ methods =>
    let ms := methods.map (STop.scan bound)
    let (s, n) := scanL (fields.filterMap (·.2.2.1))
    let self (x : String) : String := if meths.contains x then "." ++ x else x
    -- (a field's default is elaborated without `Self`: it names the
    -- top-level function, not a method or field of the class)
    (tps.flatMap (fun tp => tp.upperBound.toList.flatMap STy.fnShapes) ++
      parents.flatMap STy.fnShapes ++ fields.flatMap (·.2.1.fnShapes) ++ s ++ ms.flatMap (·.1),
      n ++ (ms.flatMap (·.2)).map self)

/-- Whether a type is comparable whatever the classes: built from the
    primitive comparable types (a generic function's `subtype(comparable)`
    parameter is matched only to such, #214). -/
partial def plainComparable : STy → Bool
  | .name n => ["int", "logic", "char", "char32", "string", "rational", "float"].contains n
  | .arr t | .opt t => plainComparable t
  | .tup ts => ts.all plainComparable
  | .map k v => plainComparable k && plainComparable v
  | _ => false

/-- A type with `string` spelled `[]char` everywhere, so that equal types
    compare equal (#231). -/
partial def normS : STy → STy
  | .name "string" => .arr (.name "char")
  | .arr t => .arr (normS t)
  | .opt t => .opt (normS t)
  | .tup ts => .tup (ts.map normS)
  | .map a b => .map (normS a) (normS b)
  | .app n ts => .app n (ts.map normS)
  | .fn ps es r => .fn (ps.map normS) es (normS r)
  | t => t

/-- `a` is `b` or a subtype the elaborator converts at a parameter or a
    result (#214): `int` to `rational`, a class to one above it, a function
    type to one whose shape is above its own at the same arguments (#503).
    Nothing else, so a value class made for a function type always
    elaborates (`TyEnv.convertsAt`). -/
def subAt (anc : String → List String) (a0 b0 : STy) : Bool :=
  let a := normS a0
  let b := normS b0
  reprStr a == reprStr b || match a, b with
    | .name "int", .name "rational" => true
    | .name x, .name y => (anc x).contains y
    | .fn ps es r, .fn qs fs u =>
      let (s, ts, r) := fnTyShape ps es r
      let (t, us, u) := fnTyShape qs fs u
      s.within t && reprStr (s.select t (ts ++ [r])) == reprStr (us ++ [u])
    | _, _ => false

/-- A match of a generic function's types (its type parameters `tps`)
    against closed ones: each parameter's type, or none. -/
partial def matchTy (tps : List String) (θ : List (String × STy)) (a b : STy) : Option (List (String × STy)) :=
  -- (`string` is `[]char`)
  let norm : STy → STy := fun | .name "string" => .arr (.name "char") | t => t
  matchTy.go tps θ (norm a) (norm b)
where
  go (tps : List String) (θ : List (String × STy)) : STy → STy → Option (List (String × STy))
  | .name x, t =>
    if tps.contains x then
      match θ.lookup x with
      | some u => if reprStr u == reprStr t then some θ else none
      | none => some ((x, t) :: θ)
    else if reprStr (STy.name x) == reprStr t then some θ else none
  | .arr a, .arr b | .opt a, .opt b => matchTy tps θ a b
  | .tup as, .tup bs => if as.length != bs.length then none else
      (as.zip bs).foldlM (fun θ (a, b) => matchTy tps θ a b) θ
  | .app n as, .app m bs => if n != m || as.length != bs.length then none else
      (as.zip bs).foldlM (fun θ (a, b) => matchTy tps θ a b) θ
  | .map a b, .map c d => (matchTy tps θ a c).bind fun θ => matchTy tps θ b d
  | .fn ps es r, .fn qs fs u =>
    -- (named parameters by name, #503)
    let (s, ps, r) := fnTyShape ps es r
    let (t, qs, u) := fnTyShape qs fs u
    if s != t then none else
      ((ps ++ [r]).zip (qs ++ [u])).foldlM (fun θ (a, b) => matchTy tps θ a b) θ
  | a, b => if reprStr a == reprStr b then some θ else none

/-- One generic value adapter, retaining symbolic types until its expected
    function type determines an instance. Empty `suffix` is the declared shape. -/
structure GenericAdapter where
  suffix : String := ""
  tparams : List TParam
  /-- Its positional parameters' types, then its named ones' (#503). -/
  params : List STy
  ret : STy
  args : List SExpr
  /-- A bare parameter replaced by tuple components, also in a receiver. -/
  subst : List (String × STy) := []
  /-- Complete relations that cannot be represented by a bound on one
      component after a whole formal becomes a tuple. -/
  relations : List (STy × STy) := []

/-- Parameters known from the value shape also determine parameters in their
    upper bounds. The converse is not inference: an upper type alone cannot
    determine an absent lower type. -/
def boundInferredNames (tps : List TParam) (types : List STy)
    (relations : List (STy × STy) := []) : List String := Id.run do
  let names := tps.map (·.name)
  let mut known := names.filter fun name => types.any (·.mentions name)
  let bounds := relations ++ tps.filterMap fun tp => tp.upperBound.map (·, STy.name tp.name)
  for _ in [0:tps.length + 1] do
    let before := known
    for (upper, lower) in bounds do
      if (lower.bareNames.filter names.contains).all known.contains then
        known := (known ++ upper.bareNames.filter names.contains).eraseDups
    if known == before then break
  return known

/-- A requested method adapter whose receiver fixes the source signature.
    Parameters are freshened before recording it, so requests are independent
    of the caller's type-variable names. -/
structure MethodRequest where
  key : String
  pos : Pos
  owner : String
  method : String
  tparams : List TParam
  receiver : STy
  params : List STy
  effs : List String
  ret : STy
  args : List SExpr
  decides : Bool
  relations : List (STy × STy) := []
  /-- The named parameters of the function type asked for (#503), last in
      `params`, and those of them a caller may omit. -/
  named : List String := []
  optional : List String := []

/-- The shape of the function type a method adapter is asked for at. -/
def MethodRequest.shape (r : MethodRequest) : Shape :=
  shapeOf r.params.length r.effs r.named r.optional

def MethodRequest.className (r : MethodRequest) (i : Nat) : String :=
  s!"{r.owner}${r.method}$fnVariance{i}"

def mergeMethodRequests (old new : List MethodRequest) : List MethodRequest :=
  new.foldl (fun acc r => if acc.any (·.key == r.key) then acc else acc ++ [r]) old

/-- A class/interface upper bound excludes tuple instances, also through a
    peer chain. An unanchored peer cycle does not establish that exclusion. -/
private def tupleInstancePossible (tps : List TParam) (name : String) : Bool :=
  go (tps.length + 1) name
where
  go : Nat → String → Bool
    | 0, _ => true
    | fuel + 1, name =>
      match (tps.find? (·.name == name)).bind (·.upperBound) with
      | none => true
      | some (.name peer) => tps.any (·.name == peer) && go fuel peer
      | some _ => false

private def tupleComparable (tps : List TParam) (name : String) : Bool :=
  -- A whole-tuple conversion to a comparable peer (possibly void) does not
  -- establish equality for each original component. A direct comparable
  -- constraint on this tuple parameter does establish it.
  (tps.find? (·.name == name)).any (·.constraint == "comparable")

/-- Tuple calls at the arities present in the program. A bare parameter can
    become the tuple of the target arguments; its comparable bound then
    belongs to every component. Existing declared-shape instances come first. -/
def genericAdapters (p : Pos) (n : String) (ps : List STy) (tps : List TParam) (r : STy)
    (arities : List Nat) (captured : List STy := []) (named : List STy := []) : List GenericAdapter := Id.run do
  let xs (k : Nat) := (List.range k).map fun i => SExpr.ident p s!"$X{i}"
  let mut out : List GenericAdapter := [{ tparams := tps, params := ps, ret := r, args := xs ps.length }]
  if arities.contains 1 then
    out := out ++ [{
      suffix := "Pack", tparams := tps, params := [.tup ps], ret := r,
      args := (List.range ps.length).map fun (i : Nat) => .app p (.ident p "$X0") [.int p (i : Int)] false }]
  match ps with
  | [.tup ts] =>
    if arities.contains ts.length then
      out := out ++ [{
        suffix := s!"Unpack{ts.length}", tparams := tps, params := ts, ret := r,
        args := [.tuple p (xs ts.length)] }]
  | [.name v] =>
    if let some tp := tps.find? (fun tp => tp.name == v && tupleInstancePossible tps v) then
      for k in arities do
        let components := (List.range k).map fun i => ({
          pos := tp.pos, name := s!"$tupleValue_{n}_{k}_{i}",
          constraint := if tupleComparable tps v then "comparable" else "type" } : TParam)
        let types := components.map fun t => STy.name t.name
        let σ := [(v, STy.tup types)]
        -- Keep the entire relation. tuple(a,b) <: t says nothing about
        -- whether a <: t or b <: t, even when t occurs only in this bound.
        let retained := tps.flatMap fun original => if original.name == v then components else
          let upper := original.upperBound.map (·.substNames σ)
          -- Keep bounds still expressible on the retained binder. Besides
          -- avoiding redundant proofs, this retains comparability implied
          -- by a nominal unique bound before field types are resolved.
          let upper := upper.filter fun | .name _ | .app .. => true | _ => false
          [{ original with
            upperBound := upper,
            constraint := if upper.isSome then original.constraint else
              if tupleComparable tps original.name then "comparable" else "type" }]
        let relations := tps.filterMap fun original => do
          let base ← original.upperBound
          let base := base.substNames σ
          if retained.any (fun kept => kept.name == original.name &&
              kept.upperBound.any (fun upper => reprStr upper == reprStr base)) then none else
            some (base, (STy.name original.name).substNames σ)
        out := out ++ [{
          suffix := s!"Unpack{k}",
          tparams := retained, relations,
          params := types, ret := r.substNames σ, args := [.tuple p (xs k)], subst := σ }]
  | _ => pure ()
  -- (the named parameters, `named`, follow the positional ones, #503)
  out := out.map fun a => { a with params := a.params ++ named.map (·.substNames a.subst) }
  -- Never introduce an unusable extra class merely because a different
  -- function type was written elsewhere. The original adapter is unchanged.
  return out.take 1 ++ (out.drop 1).filter fun a =>
    let known := boundInferredNames a.tparams (a.params ++ [a.ret] ++ captured.map (·.substNames a.subst)) a.relations
    a.tparams.all fun tp => known.contains tp.name

def parentName : STy → Option String
  | .name q | .app q _ => some q
  | _ => none

/-- Each class's name, parents, fields and methods. -/
def classDefs (tops : List STop) : List (String × List STy × List String × List String) :=
  tops.filterMap fun
    | .classDef _ n _ _ ps _ fs _ ms => some (n, ps, fs.map (·.1), ms.filterMap fun
        | .fn _ m .. => some m
        | _ => none)
    | _ => none

/-- The function types each definition of `tops` and `extra` writes, and
    the names it uses as values (`STop.scan`; in a class's methods, its
    fields and methods, its own and its parents', are meant). -/
def scanTops (tops extra : List STop) : List (List Shape × List String) :=
  let defs := classDefs tops
  let rec fieldsOf (fuel : Nat) (c : String) : List String :=
    match fuel, defs.find? (·.1 == c) with
    | fuel + 1, some (_, ps, fs, _) => fs ++ (ps.filterMap parentName).flatMap (fieldsOf fuel)
    | _, _ => []
  let rec methodsOf (fuel : Nat) (c : String) : List String :=
    match fuel, defs.find? (·.1 == c) with
    | fuel + 1, some (_, ps, _, ms) => ms ++ (ps.filterMap parentName).flatMap (methodsOf fuel)
    | _, _ => []
  (tops ++ extra).map fun t => match t with
    | .classDef _ n .. => t.scan (fieldsOf (defs.length + 1) n) (methodsOf (defs.length + 1) n)
    | _ => t.scan

/-- A function's own shape, its named parameters optional where they have
    defaults (#503), and its parameters' types in that shape's order. -/
def ownShape (ps : List SParam) (effs : List String) : Shape × List STy :=
  let (s, order) := shapeOfParams (ps.map fun q => if q.named then some (q.name, q.default.isSome) else none) effs
  (s, order.filterMap fun i => ps[i]?.map (·.ty))

/-- The `$call…` implementations of a value class of shape `own` at `targs`
    (its parameters' types, then its result's): one per closed shape among
    `fits`, taking that shape's parameters (positional ones as `$X0`…, named
    ones by name) and calling `call` with the positional arguments `pargs`
    and the named ones that shape has. A named parameter it lacks is not
    passed, so the function's own default fills it in at the call, in the
    function's scope (#503). -/
def callMethods (p : Pos) (own : Shape) (targs : List STy) (fits : List Shape) (pargs : List SExpr)
    (call : List SExpr → SExpr) : List STop :=
  (fits.filter (·.closed)).map fun s =>
    let ts := own.select s targs
    let params := (ts.take s.positional).zipIdx.map (fun (t, i) => ({ name := s!"$X{i}", ty := t } : SParam)) ++
      (s.named.zip (ts.drop s.positional)).map fun (n, t) => { name := n, ty := t, named := true }
    .fn p s.call params [] (s.effs ++ ["override"]) (ts.getLastD (.name "void"))
      (call (pargs ++ s.named.map fun n => .decl p s!"?{n}" none false (.ident p n)))

/-- The interfaces a value class of shape `own` at `targs` implements: its
    own shape first (the value's type when nothing else gives one), then
    the other shapes it fits. -/
def classParents (own : Shape) (targs : List STy) (fits : List Shape) : List STy :=
  (own :: fits.filter (· != own)).map fun s => STy.app s.name (own.select s targs)

/-- Add the shapes' interfaces and the value classes of the functions used
    as values (#210). A function is used as a value when its name occurs
    other than as the head of a call (an over-approximation: a parameter of
    that name may be meant, and then the class is never used). Overloaded
    functions and hidden ones get none (the elaborator explains why such a
    function is no value). -/
def desugar (tops : List STop) (extra : List STop := []) (requests : List (String × STy) := [])
    (methodRequests : List MethodRequest := []) (written : List STop := []) :
    List STop := Id.run do
  let defs := classDefs tops
  let scans := scanTops tops extra
  let named := (scans.flatMap (·.2)).eraseDups
  -- (#503) a function with named parameters only where the program as
  -- written names it as a value: the choice inliner's markers name the
  -- functions with several values they inline as arguments too
  let writtenNamed := if written.isEmpty then named else ((scanTops written []).flatMap (·.2)).eraseDups
  -- (and none whose named parameter has its name, which would hide it in
  -- its value class's call of it)
  let valueAt (n : String) (ps : List SParam) : Bool :=
    named.contains n && (ps.all (!·.named) || writtenNamed.contains n && !ps.any (·.name == n))
  let fnNames := tops.filterMap fun | .fn _ n .. => some n | _ => none
  let values : List (Pos × String × List SParam × List String × STy) := tops.filterMap fun
    | .fn p n ps tps effs r _ =>
      if valueAt n ps && tps.isEmpty && !n.contains '$' &&
          (fnNames.filter (· == n)).length == 1 then some (p, n, ps, effs, r)
      else none
    | _ => none
  -- methods used as values (`X.M`, or `M` in the class's methods): each
  -- declaring class's method, its receiver a field `$self` (#210)
  let members := named.filterMap fun n => if n.startsWith "." then some (n.drop 1).toString else none
  -- (the declaration an override overrides: the nearest class or interface
  -- above that declares the method)
  let classOf (c : String) : Option (List TParam × List STy × List STop) := tops.findSome? fun
    | .classDef _ n tps _ ps _ _ _ ms => if n == c then some (tps, ps, ms) else none
    | _ => none
  let rec declOf (fuel : Nat) (c m : String) : Option (List TParam × List STy × List String) :=
    match fuel, classOf c with
    | fuel + 1, some (_, ps, _) => (ps.filterMap parentName).findSome? fun q =>
      match classOf q with
      | some (qtps, _, qms) =>
        let own : STop → Option (List STy × List String) := fun
          | .fn _ m' qps _ qeffs qr _ =>
            if m' == m && !qeffs.contains "override" then some (qps.map (·.ty) ++ [qr], (ownShape qps qeffs).1.optional)
            else none
          | _ => none
        match qms.findSome? own with
        | some (targs, optional) => some (qtps, targs, optional)
        | none => declOf fuel q m
      | none => none
    | _, _ => none
  let mvalues : List (Pos × String × List TParam × List TParam × String × List SParam × List String × STy) :=
    tops.flatMap fun
      | .classDef _ c tps _ _ _ _ _ ms => ms.filterMap fun
        | .fn mp m ps mtps effs r b =>
          let targs := ps.map (·.ty) ++ [r]
          -- An override with a different signature needs its own value
          -- class (a narrower result, #219; defaults for other named
          -- parameters, #503). Otherwise the declaration's adapter already
          -- dispatches to it, including generic receivers; duplicating
          -- adapters along a chain grows their dispatch again.
          let needed := !effs.contains "override" || match declOf (tops.length + 1) c m with
            | some (_, dtargs, doptional) =>
              dtargs.length != targs.length ||
                (dtargs.zip targs).any (fun (a, b) => reprStr a != reprStr b) ||
                doptional != (ownShape ps effs).1.optional
            | none => true
          -- Repeated, compound and hidden receiver arguments use ordinary
          -- GADT dispatch. The captured receiver retains their witnesses.
          -- (an overloaded method is no value; so is one that, without
          -- <override>, takes a name its class inherits: it overloads that
          -- name, which every receiver that sees it sees too)
          let overloaded := (ms.filter fun | .fn _ m' .. => m' == m | _ => false).length > 1 ||
            !effs.contains "override" && (declOf (tops.length + 1) c m).isSome
          -- Member scanning also sees unrelated fields. A parameter absent
          -- from the signature can never be inferred at value creation, and
          -- an unused adapter would itself contain an uninferrable call.
          let known := boundInferredNames (tps ++ mtps) (targs ++ [STy.app c (tps.map fun tp => .name tp.name)])
          let inferable := mtps.all fun tp => known.contains tp.name
          -- (#283) and none for a family's stub: a method with several values
          -- is no value (`Choice.methodFns` refuses one as a value)
          if members.contains m && valueAt ("." ++ m) ps && needed && !overloaded && inferable && !m.contains '$' &&
              !m.startsWith "(" && !Choice.isFamilyStub b then
            -- Keep method parameters apart from the receiver arguments a
            -- caller substitutes: its `u` may be a different method's `u`.
            let names := mtps.zipIdx.map fun (tp, i) => (tp.name, s!"$methodValue_{c}_{m}_{i}")
            let σ := names.map fun (a, b) => (a, STy.name b)
            some (mp, c, tps, mtps.map (·.rename names), m,
              ps.map (fun sp => { sp with ty := sp.ty.substNames σ }), effs, r.substNames σ)
          else none
        | _ => none
      | _ => []
  let gvalues : List (Pos × String × List SParam × List TParam × List String × STy) := tops.filterMap fun
    | .fn p n ps tps effs r _ =>
      if valueAt n ps && !tps.isEmpty && !n.contains '$' &&
          (fnNames.filter (· == n)).length == 1 then some (p, n, ps, tps, effs, r)
      else none
    | _ => none
  -- (#214) the function types each function is asked for at: where the
  -- elaborator wanted it as a value and no class of its fitted
  let requested (n : String) : List (List STy × List String × STy) := requests.filterMap fun (f, t) =>
    if f == n then match t with
      | .fn qs es u => some (qs, es, u)
      | _ => none
    else none
  let rec ancOf (fuel : Nat) (c : String) : List String :=
    match fuel, defs.find? (·.1 == c) with
    | fuel + 1, some (_, ps, _, _) =>
      -- (through generic parents too: subtyping is by name, #214)
      let up := ps.filterMap parentName
      up ++ up.flatMap (ancOf fuel)
    | _, _ => []
  let anc := ancOf (defs.length + 1)
  if values.isEmpty && mvalues.isEmpty && gvalues.isEmpty && requests.isEmpty && methodRequests.isEmpty &&
      (scans.all fun (s, _) => s.isEmpty) then return tops
  -- every shape written, and each value's own (a value's type when nothing
  -- else gives one)
  let mut shapes : List Shape := []
  for s in scans.flatMap (·.1) ++ values.map (fun (_, _, ps, effs, _) => (ownShape ps effs).1) ++
      gvalues.map (fun (_, _, ps, _, effs, _) => (ownShape ps effs).1) ++
      mvalues.map (fun (_, _, _, _, _, ps, effs, _) => (ownShape ps effs).1) ++
      methodRequests.flatMap (fun r => r.shape ::
        r.receiver.fnShapes ++ r.params.flatMap STy.fnShapes ++ r.ret.fnShapes ++
        r.tparams.flatMap (fun tp => tp.upperBound.toList.flatMap STy.fnShapes) ++
        r.relations.flatMap (fun (upper, lower) => upper.fnShapes ++ lower.fnShapes)) ++
      requests.flatMap (fun (_, ty) => ty.fnShapes) do
    if !shapes.contains s then shapes := shapes ++ [s]
  -- (tuple adapters change the positional parameters, #231)
  let arities := (shapes.map (·.positional)).eraseDups
  -- (a generic function's or a method's adapters: of its own shape with
  -- their positional parameters, the named ones after, #503)
  let adapters (p : Pos) (n : String) (ps : List SParam) (tps : List TParam) (effs : List String) (r : STy)
      (captured : List STy) : Shape × List GenericAdapter :=
    let (own, ts) := ownShape ps effs
    (own, genericAdapters p n (ts.take own.positional) tps r arities captured (ts.drop own.positional))
  for (p, n, ps, tps, effs, r) in gvalues do
    let (own, as) := adapters p n ps tps effs r []
    for a in as do
      let s := { own with arity := a.params.length }
      if !shapes.contains s then shapes := shapes ++ [s]
  for (p, c, ctps, mtps, m, ps, effs, r) in mvalues do
    let selfTy := STy.app c (ctps.map fun tp => .name tp.name)
    let (own, as) := adapters p s!"{c}${m}" ps (ctps ++ mtps) effs r [selfTy]
    for a in as do
      let s := { own with arity := a.params.length }
      if !shapes.contains s then shapes := shapes ++ [s]
  let p0 : Pos := match tops.head? with
    | some (.fn p ..) | some (.const p ..) | some (.classDef p ..) => p
    | none => { line := 0, col := 0 }
  let vars (k : Nat) : List STy := (List.range k).map (fun i => STy.name s!"$a{i}") ++ [.name "$r"]
  let tps (k : Nat) : List TParam :=
    ((List.range k).map fun i => { pos := p0, name := s!"$a{i}", constraint := "type" }) ++
      [{ pos := p0, name := "$r", constraint := "type" }]
  let xs (p : Pos) (k : Nat) : List SExpr := (List.range k).map fun i => SExpr.ident p s!"$X{i}"
  let mut out : List STop := []
  -- each shape's interface: above it, the shapes it is within (more
  -- effects, fewer names) at its arguments for theirs; a closed one's
  -- abstract method (an open one's are those of the closed ones above it)
  for s in shapes do
    let k := s.arity
    let parents := (shapes.filter fun t => t != s && s.within t).map fun t => STy.app t.name (s.select t (vars k))
    let call : STop := .fn p0 s.call ((List.range k).map fun i =>
        if i < s.positional then { name := s!"$X{i}", ty := .name s!"$a{i}" }
        else { name := s.named[i - s.positional]!, ty := .name s!"$a{i}", named := true })
      [] (s.effs ++ ["$abstract"]) (.name "$r") (.block p0 [])
    out := out ++ [.classDef p0 s.name (tps k) [] parents true [] [] (if s.closed then [call] else [])]
  for (p, n, ps, effs, r) in values do
    let (own, ts) := ownShape ps effs
    let fits := shapes.filter (own.within ·)
    out := out ++ [.classDef p s!"{n}$fn" [] [] (classParents own (ts ++ [r]) fits) false [] []
      (callMethods p own (ts ++ [r]) fits (xs p own.positional) fun args => .app p (.ident p n) args own.decides)]
  -- (#214) a value class per closed function type `t` (its parameters' and
  -- result's types `ts`) a value of shape `own` is asked for at and fits
  -- other than at its own types, `owner`, implementing `t`'s shape (and
  -- those above it) at the type's own arguments; `pargs` are the positional
  -- arguments of `call`
  let variant (p : Pos) (owner : String) (own t : Shape) (ts : List STy) (pargs : List SExpr)
      (call : List SExpr → SExpr) (fields : List (String × STy × Option SExpr × Bool) := []) : Option STop :=
    -- (the effects and names only: a tuple parameter may be flattened, #231)
    if !{ own with arity := t.positional + own.named.length }.within t then none else
    let fits := shapes.filter (t.within ·)
    some (.classDef p owner [] [] (classParents t ts fits) false fields [] (callMethods p t ts fits pargs call))
  -- (#503) the types of the named parameters `t` names, of a function of
  -- shape `own` with parameter types `ts`, when it has them all
  let namedAt (own t : Shape) (ts : List STy) : Option (List STy) :=
    t.named.mapM fun n => (own.named.idxOf? n).bind (ts[own.positional + ·]?)
  -- (#231) the parameters a function takes as a function type wants them:
  -- as they are, its single tuple parameter unflattened into the type's
  -- parameters (the call makes the tuple), or its parameters flattened into
  -- the type's single tuple parameter (the call takes the tuple apart);
  -- the function's parameter types to compare with, and the call's
  -- arguments
  let reshape (p : Pos) (ps : List STy) (qs : List STy) : Option (List STy × List STy × List SExpr) :=
    let xs (k : Nat) : List SExpr := (List.range k).map fun i => SExpr.ident p s!"$X{i}"
    if qs.length == ps.length then some (ps, qs, xs qs.length)
    else match ps, qs with
      | [.tup es], _ =>
        if es.length == qs.length then some (es, qs, [.tuple p (xs qs.length)]) else none
      | _, [.tup es] =>
        if es.length == ps.length then
          some (ps, es, (List.range ps.length).map fun (i : Nat) => SExpr.app p (.ident p "$X0") [.int p (i : Int)] false)
        else none
      -- (a single parameter of another type, a type parameter say, at the
      -- tuple of the type's parameters: matching decides)
      | [_], _ => if qs.length ≥ 2 then some (ps, [.tup qs], [.tuple p (xs qs.length)]) else none
      | _, _ => none
  -- (the arguments `ts` of shape `own` give `t`'s, `us`, as they are)
  let exactly (own t : Shape) (ts us : List STy) : Bool :=
    own.within t && let vs := own.select t ts
    vs.length == us.length && (vs.zip us).all fun (a, b) => reprStr (normS a) == reprStr (normS b)
  for (p, n, ps, effs, r) in values do
    let (own, ts) := ownShape ps effs
    let mut k := 0
    for (qs, es, u) in requested n do
      let (t, tqs, u) := fnTyShape qs es u
      let some (ps', qs', args) := reshape p (ts.take own.positional) (tqs.take t.positional) | continue
      let some named := namedAt own t ts | continue
      -- (contravariant parameters, a covariant result)
      if !exactly own t (ts ++ [r]) (tqs ++ [u]) && (qs'.zip ps').all (fun (a, b) => subAt anc a b) &&
          ((tqs.drop t.positional).zip named).all (fun (a, b) => subAt anc a b) && subAt anc r u then
        if let some c := variant p s!"{n}$fn${k}" own t (tqs ++ [u]) args
            (fun args => .app p (.ident p n) args own.decides) then
          out := out ++ [c]
          k := k + 1
  for (p, n, ps, tps, effs, r) in gvalues do
    let (own, as) := adapters p n ps tps effs r []
    for a in as do
      let sh := { own with arity := a.params.length }
      let fits := shapes.filter (sh.within ·)
      let owner := s!"{n}$fn{a.suffix}"
      out := out ++ [.classDef p owner a.tparams [] (classParents sh (a.params ++ [a.ret]) fits) false
        (SubtypeEvidence.relationFields p owner a.relations) []
        (callMethods p sh (a.params ++ [a.ret]) fits a.args fun args => .app p (.ident p n) args own.decides)]
    let ts := (ownShape ps effs).2
    let tpn := tps.map (·.name)
    let mut k := 0
    for (qs, es, u) in requested n do
      let (t, tqs, u) := fnTyShape qs es u
      let some (ps', qs', args) := reshape p (ts.take own.positional) (tqs.take t.positional) | continue
      let some named := namedAt own t ts | continue
      let θ := ((ps' ++ named ++ [r]).zip (qs' ++ tqs.drop t.positional ++ [u])).foldlM
        (fun θ (a, b) => matchTy tpn θ a b) []
      if let some θ := θ then
        -- (every type parameter instantiated, a comparable one to a type
        -- that is surely comparable)
        if tps.all fun tp => match θ.lookup tp.name with
            | some t => tp.constraint != "comparable" || plainComparable t
            | none => false then
          if let some c := variant p s!"{n}$fn${k}" own t (tqs ++ [u]) args
              (fun args => .app p (.ident p n) args own.decides) then
            out := out ++ [c]
            k := k + 1
  for (p, c, ctps, mtps, m, ps, effs, r) in mvalues do
    let selfTy : STy := if ctps.isEmpty then .name c else .app c (ctps.map fun tp => .name tp.name)
    let call (args : List SExpr) : SExpr := .app p (.member p (.ident p "$self") m) args (effs.contains "decides")
    let (own, as) := adapters p s!"{c}${m}" ps (ctps ++ mtps) effs r [selfTy]
    for a in as do
      let sh := { own with arity := a.params.length }
      let fits := shapes.filter (sh.within ·)
      let owner := s!"{c}${m}$fn{a.suffix}"
      out := out ++ [.classDef p owner a.tparams [] (classParents sh (a.params ++ [a.ret]) fits) false
        ([("$self", selfTy.substNames a.subst, none, false)] ++
          SubtypeEvidence.relationFields p owner a.relations) [] (callMethods p sh (a.params ++ [a.ret]) fits a.args call)]
    -- (#231) a method of a class without type parameters as a value at a
    -- closed function type it fits by variance, asked for as `.{c}${m}`:
    -- `{c}${m}$fn${k}`, holding the receiver
    if ctps.isEmpty && mtps.isEmpty then
      let ts := (ownShape ps effs).2
      let mut k := 0
      for (qs, es, u) in requested s!".{c}${m}" do
        let (t, tqs, u) := fnTyShape qs es u
        let some named := namedAt own t ts | continue
        if !exactly own t (ts ++ [r]) (tqs ++ [u]) && t.positional == own.positional &&
            (tqs.zip (ts.take own.positional ++ named)).all (fun (a, b) => subAt anc a b) && subAt anc r u then
          if let some v := variant p s!"{c}${m}$fn${k}" own t (tqs ++ [u]) (xs p own.positional) call
              [("$self", .name c, none, false)] then
            out := out ++ [v]
            k := k + 1
  for (r, i) in methodRequests.zipIdx do
    let own := r.shape
    let fits := shapes.filter fun s => s != own && own.within s
    out := out ++ [.classDef r.pos (r.className i) r.tparams [] (classParents own (r.params ++ [r.ret]) fits) false
      (SubtypeEvidence.relationFields r.pos (r.className i) r.relations ++
        [("$self", r.receiver, none, false)]) []
      (callMethods r.pos own (r.params ++ [r.ret]) (own :: fits) r.args fun args =>
        .app r.pos (.member r.pos (.ident r.pos "$self") r.method) args r.decides)]
  return tops ++ out

end FnValues

end OpenVerse.Front
