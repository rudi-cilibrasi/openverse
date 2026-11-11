import OpenVerse.Front.Syntax

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

/-- A function type's arity and effects: the hidden interface it is an
    instance of. -/
structure Shape where
  arity : Nat
  decides : Bool := false
  suspends : Bool := false
  /-- The heap effects it allows, in `heapFx`'s order. -/
  fx : List String := heapFx
  deriving BEq, Repr, Inhabited

def shapeOf (arity : Nat) (effs : List String) : Shape :=
  { arity, decides := effs.contains "decides", suspends := effs.contains "suspends", fx := allowedFx effs }

/-- The effect specifiers that give a shape's effects. -/
def Shape.effs (s : Shape) : List String :=
  (if s.decides then ["decides"] else []) ++ (if s.suspends then ["suspends"] else []) ++
  (if s.fx == heapFx then [] else if s.fx.isEmpty then ["computes"] else s.fx)

/-- The effects part of a shape's names: `:decides:reads`, say. -/
def Shape.tag (s : Shape) : String := String.join (s.effs.map (":" ++ ·))

/-- The hidden interface of a shape. -/
def Shape.name (s : Shape) : String := s!"$fn{s.arity}{s.tag}"

/-- The hidden interface's method. -/
def Shape.call (s : Shape) : String := s!"$call{s.tag}"

/-- Whether `n` is a shape's interface; its arity and effects. -/
def parseName (n : String) : Option (Nat × List String) :=
  if !n.startsWith "$fn" then none else
  match (n.drop 3).toString.splitOn ":" with
  | a :: effs => a.toNat?.map fun k => (k, effs)
  | [] => none

/-- The method a value of shape interface `n` is called through. -/
def callOf (n : String) : String :=
  match parseName n with
  | some (k, effs) => (shapeOf k effs).call
  | none => "$call"

/-- A function type as Verse writes it: `type{_(:int, :string)<decides>:float}`. -/
def showFn (effs : List String) (ps : List String) (r : String) : String :=
  "type{_(" ++ ", ".intercalate (ps.map (":" ++ ·)) ++ ")" ++ String.join (effs.map fun e => s!"<{e}>") ++
    ":" ++ r ++ "}"

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

/-- `s`'s effects are among `t`'s: a function of shape `s` is one of shape
    `t` too. -/
def Shape.within (s t : Shape) : Bool :=
  s.arity == t.arity && (!s.decides || t.decides) && (!s.suspends || t.suspends) && s.fx.all t.fx.contains

partial def _root_.OpenVerse.Front.STy.fnShapes : STy → List Shape
  | .name _ => []
  | .arr t | .opt t => t.fnShapes
  | .tup ts | .app _ ts => ts.flatMap STy.fnShapes
  | .map a b => a.fnShapes ++ b.fnShapes
  | .fn ps es r =>
    -- (a type both <decides> and <suspends> has none: `resolveTy` refuses it)
    let s := shapeOf ps.length es
    (if s.decides && s.suspends then [] else [s]) ++ ps.flatMap STy.fnShapes ++ r.fnShapes

/-- The type names an expression mentions: in its types and constructions. -/
partial def _root_.OpenVerse.Front.SExpr.tyNames : SExpr → List String
  | .decl _ _ t _ e => (t.map STy.allNames).getD [] ++ e.tyNames
  | .construct _ n ts args => n :: ts.flatMap STy.allNames ++ args.flatMap SExpr.tyNames
  | .app _ f args _ => f.tyNames ++ args.flatMap SExpr.tyNames
  | .member _ e _ | .query _ e | .neg _ e | .notE _ e | .optionLit _ e | .logicLit _ e | .loop _ e
  | .gen _ _ _ e => e.tyNames
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b => a.tyNames ++ b.tyNames
  | .cmp _ a rest => a.tyNames ++ rest.flatMap (·.2.tyNames)
  | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap SExpr.tyNames
  | .ite _ cs t e => cs.flatMap SExpr.tyNames ++ t.tyNames ++ (e.map SExpr.tyNames).getD []
  | .forE _ cs b => cs.flatMap SExpr.tyNames ++ b.tyNames
  | .ret _ e => (e.map SExpr.tyNames).getD []
  | .caseE _ e arms => e.tyNames ++ arms.flatMap fun (q, v) => (q.map SExpr.tyNames).getD [] ++ v.tyNames
  | .set _ l _ e => l.tyNames ++ e.tyNames
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => k.tyNames ++ v.tyNames
  | .structDef _ _ fs => fs.flatMap fun (_, t, d, _) => t.allNames ++ (d.map SExpr.tyNames).getD []
  | .refineDef _ _ t cs => t.allNames ++ cs.flatMap SExpr.tyNames
  | .str _ parts => parts.flatMap fun | .code e => e.tyNames | .text _ => []
  | _ => []

/-- Whether a definition mentions the type `n`. -/
partial def _root_.OpenVerse.Front.STop.usesType (n : String) : STop → Bool
  | .fn _ _ ps _ _ r body =>
    (ps.flatMap (·.ty.allNames) ++ r.allNames ++ body.tyNames).contains n
  | .const _ _ t e => ((t.map STy.allNames).getD [] ++ e.tyNames).contains n
  | .classDef _ _ _ _ parents _ fields _ methods =>
    (parents.flatMap STy.allNames ++ fields.flatMap (fun (_, t, d, _) => t.allNames ++ (d.map SExpr.tyNames).getD [])).contains n ||
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
  | .structDef _ _ fs =>
    let (s, n) := scanL (fs.filterMap (·.2.2.1))
    (fs.flatMap (·.2.1.fnShapes) ++ s, n)
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
  | .fn _ _ ps _ _ r body =>
    let (s, n) := scanL [body]
    let pss := ps.map SParam.scan
    let mine := ps.map (·.name) ++ bound
    (r.fnShapes ++ pss.flatMap (·.1) ++ s, (pss.flatMap (·.2) ++ n).filter (!mine.contains ·))
  | .const _ _ t e =>
    let (s, n) := e.scan
    ((t.map STy.fnShapes).getD [] ++ s, n)
  | .classDef _ _ _ _ parents _ fields _ methods =>
    let ms := methods.map (STop.scan bound)
    let (s, n) := scanL (fields.filterMap (·.2.2.1))
    let self (x : String) : String := if meths.contains x then "." ++ x else x
    -- (a field's default is elaborated without `Self`: it names the
    -- top-level function, not a method or field of the class)
    (parents.flatMap STy.fnShapes ++ fields.flatMap (·.2.1.fnShapes) ++ s ++ ms.flatMap (·.1),
      n ++ (ms.flatMap (·.2)).map self)

/-- The function types inside a type: parameters, effects, result. -/
partial def _root_.OpenVerse.Front.STy.fnTypes : STy → List (List STy × List String × STy)
  | .name _ => []
  | .arr t | .opt t => t.fnTypes
  | .tup ts | .app _ ts => ts.flatMap STy.fnTypes
  | .map a b => a.fnTypes ++ b.fnTypes
  | .fn ps es r =>
    -- (a type both <decides> and <suspends> has no shape: refused later)
    (if es.contains "decides" && es.contains "suspends" then [] else [(ps, es, r)]) ++
      ps.flatMap STy.fnTypes ++ r.fnTypes

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
    result (#214): `int` to `rational`, a class to one above it. Nothing
    else, so a value class made for a function type always elaborates. -/
def subAt (anc : String → List String) (a0 b0 : STy) : Bool :=
  let a := normS a0
  let b := normS b0
  reprStr a == reprStr b || match a, b with
    | .name "int", .name "rational" => true
    | .name x, .name y => (anc x).contains y
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
    if ps.length != qs.length || shapeOf ps.length es != shapeOf qs.length fs then none else
      ((ps ++ [r]).zip (qs ++ [u])).foldlM (fun θ (a, b) => matchTy tps θ a b) θ
  | a, b => if reprStr a == reprStr b then some θ else none

/-- One generic value adapter, retaining symbolic types until its expected
    function type determines an instance. Empty `suffix` is the declared shape. -/
structure GenericAdapter where
  suffix : String := ""
  tparams : List TParam
  params : List STy
  ret : STy
  args : List SExpr
  /-- A bare parameter replaced by tuple components, also in a receiver. -/
  subst : List (String × STy) := []

/-- Tuple calls at the arities present in the program. A bare parameter can
    become the tuple of the target arguments; its comparable bound then
    belongs to every component. Existing declared-shape instances come first. -/
def genericAdapters (p : Pos) (n : String) (ps : List STy) (tps : List TParam) (r : STy)
    (arities : List Nat) (captured : List STy := []) : List GenericAdapter := Id.run do
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
    if let some tp := tps.find? (·.name == v) then
      for k in arities do
        let components := (List.range k).map fun i => { tp with name := s!"$tupleValue_{n}_{k}_{i}" }
        let types := components.map fun t => STy.name t.name
        let σ := [(v, STy.tup types)]
        out := out ++ [{
          suffix := s!"Unpack{k}",
          tparams := tps.flatMap (fun t => if t.name == v then components else [t]),
          params := types, ret := r.substNames σ, args := [.tuple p (xs k)], subst := σ }]
  | _ => pure ()
  -- Never introduce an unusable extra class merely because a different
  -- function type was written elsewhere. The original adapter is unchanged.
  return out.take 1 ++ (out.drop 1).filter fun a =>
    a.tparams.all fun tp => (a.params ++ [a.ret] ++ captured.map (·.substNames a.subst)).any (·.mentions tp.name)

/-- Add the shapes' interfaces and the value classes of the functions used
    as values (#210). A function is used as a value when its name occurs
    other than as the head of a call (an over-approximation: a parameter of
    that name may be meant, and then the class is never used). Generic and
    overloaded functions, functions with named parameters and hidden ones
    get none (the elaborator explains why such a function is no value). -/
def desugar (tops : List STop) (extra : List STop := []) (requests : List (String × STy) := []) :
    List STop := Id.run do
  -- (each class's fields, its own and its parents', in its methods: a
  -- field of that name is meant there)
  let defs : List (String × List STy × List String × List String) := tops.filterMap fun
    | .classDef _ n _ _ ps _ fs _ ms => some (n, ps, fs.map (·.1), ms.filterMap fun
        | .fn _ m .. => some m
        | _ => none)
    | _ => none
  let parentName : STy → Option String := fun | .name q | .app q _ => some q | _ => none
  let rec fieldsOf (fuel : Nat) (c : String) : List String :=
    match fuel, defs.find? (·.1 == c) with
    | fuel + 1, some (_, ps, fs, _) => fs ++ (ps.filterMap parentName).flatMap (fieldsOf fuel)
    | _, _ => []
  let rec methodsOf (fuel : Nat) (c : String) : List String :=
    match fuel, defs.find? (·.1 == c) with
    | fuel + 1, some (_, ps, _, ms) => ms ++ (ps.filterMap parentName).flatMap (methodsOf fuel)
    | _, _ => []
  let scans := (tops ++ extra).map fun t => match t with
    | .classDef _ n .. => t.scan (fieldsOf (defs.length + 1) n) (methodsOf (defs.length + 1) n)
    | _ => t.scan
  let named := (scans.flatMap (·.2)).eraseDups
  let fnNames := tops.filterMap fun | .fn _ n .. => some n | _ => none
  let values : List (Pos × String × List SParam × List String × STy) := tops.filterMap fun
    | .fn p n ps tps effs r _ =>
      if named.contains n && tps.isEmpty && ps.all (!·.named) && !n.contains '$' &&
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
  let rec declOf (fuel : Nat) (c m : String) : Option (List TParam × List STy) :=
    match fuel, classOf c with
    | fuel + 1, some (_, ps, _) => (ps.filterMap parentName).findSome? fun q =>
      match classOf q with
      | some (qtps, _, qms) =>
        let own : STop → Option (List STy) := fun
          | .fn _ m' qps _ qeffs qr _ =>
            if m' == m && !qeffs.contains "override" then some (qps.map (·.ty) ++ [qr]) else none
          | _ => none
        match qms.findSome? own with
        | some targs => some (qtps, targs)
        | none => declOf fuel q m
      | none => none
    | _, _ => none
  let mvalues : List (Pos × String × List TParam × List TParam × String × List SParam × List String × STy) :=
    tops.flatMap fun
      | .classDef _ c tps _ _ _ _ _ ms => ms.filterMap fun
        | .fn mp m ps mtps effs r _ =>
          let targs := ps.map (·.ty) ++ [r]
          -- An override with a different signature needs its own value
          -- class (a narrower result, #219). Otherwise the declaration's
          -- adapter already dispatches to it, including generic receivers;
          -- duplicating adapters along a chain grows their dispatch again.
          let needed := !effs.contains "override" || match declOf (tops.length + 1) c m with
            | some (_, dtargs) =>
              dtargs.length != targs.length ||
                (dtargs.zip targs).any fun (a, b) => reprStr a != reprStr b
            | none => true
          -- Repeated, compound and hidden receiver arguments use ordinary
          -- GADT dispatch. The captured receiver retains their witnesses.
          let overloaded := (ms.filter fun | .fn _ m' .. => m' == m | _ => false).length > 1
          -- Member scanning also sees unrelated fields. A parameter absent
          -- from the signature can never be inferred at value creation, and
          -- an unused adapter would itself contain an uninferrable call.
          let inferable := mtps.all fun tp => targs.any (·.mentions tp.name)
          if members.contains m && needed && !overloaded && inferable && ps.all (!·.named) && !m.contains '$' &&
              !m.startsWith "(" then
            -- Keep method parameters apart from the receiver arguments a
            -- caller substitutes: its `u` may be a different method's `u`.
            let names := mtps.zipIdx.map fun (tp, i) => (tp.name, s!"$methodValue_{c}_{m}_{i}")
            let σ := names.map fun (a, b) => (a, STy.name b)
            some (mp, c, tps, mtps.map (fun tp => { tp with name := (names.lookup tp.name).getD tp.name }), m,
              ps.map (fun sp => { sp with ty := sp.ty.substNames σ }), effs, r.substNames σ)
          else none
        | _ => none
      | _ => []
  let gvalues : List (Pos × String × List SParam × List TParam × List String × STy) := tops.filterMap fun
    | .fn p n ps tps effs r _ =>
      if named.contains n && !tps.isEmpty && ps.all (!·.named) && !n.contains '$' &&
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
  if values.isEmpty && mvalues.isEmpty && gvalues.isEmpty && (scans.all fun (s, _) => s.isEmpty) then return tops
  -- every shape written, and each value's own (a value's type when nothing
  -- else gives one)
  let mut shapes : List Shape := []
  for s in scans.flatMap (·.1) ++ values.map (fun (_, _, ps, effs, _) => shapeOf ps.length effs) ++
      gvalues.map (fun (_, _, ps, _, effs, _) => shapeOf ps.length effs) ++
      mvalues.map (fun (_, _, _, _, _, ps, effs, _) => shapeOf ps.length effs) do
    if !shapes.contains s then shapes := shapes ++ [s]
  let arities := (shapes.map (·.arity)).eraseDups
  for (p, n, ps, tps, effs, r) in gvalues do
    for a in genericAdapters p n (ps.map (·.ty)) tps r arities do
      let s := shapeOf a.params.length effs
      if !shapes.contains s then shapes := shapes ++ [s]
  for (p, c, ctps, mtps, m, ps, effs, r) in mvalues do
    let selfTy := STy.app c (ctps.map fun tp => .name tp.name)
    for a in genericAdapters p s!"{c}${m}" (ps.map (·.ty)) (ctps ++ mtps) r arities [selfTy] do
      let s := shapeOf a.params.length effs
      if !shapes.contains s then shapes := shapes ++ [s]
  let p0 : Pos := match tops.head? with
    | some (.fn p ..) | some (.const p ..) | some (.classDef p ..) => p
    | none => { line := 0, col := 0 }
  let vars (k : Nat) : List STy := (List.range k).map (fun i => STy.name s!"$a{i}") ++ [.name "$r"]
  let tps (k : Nat) : List TParam :=
    ((List.range k).map fun i => { pos := p0, name := s!"$a{i}", constraint := "type" }) ++
      [{ pos := p0, name := "$r", constraint := "type" }]
  let params (ts : List STy) : List SParam :=
    (ts.zip (List.range ts.length)).map fun (t, i) => { name := s!"$X{i}", ty := t }
  let mut out : List STop := []
  for s in shapes do
    let k := s.arity
    let parents := (shapes.filter fun t => t != s && s.within t).map fun t => STy.app t.name (vars k)
    let call : STop := .fn p0 s.call (params ((vars k).take k)) [] (s.effs ++ ["$abstract"]) (.name "$r") (.block p0 [])
    out := out ++ [.classDef p0 s.name (tps k) [] parents true [] [] [call]]
  for (p, n, ps, effs, r) in values do
    let own := shapeOf ps.length effs
    let fits := shapes.filter (own.within ·)
    let targs := ps.map (·.ty) ++ [r]
    let args := (List.range ps.length).map fun i => SExpr.ident p s!"$X{i}"
    let methods := fits.map fun s =>
      STop.fn p s.call (params (ps.map (·.ty))) [] (s.effs ++ ["override"]) r
        (.app p (.ident p n) args own.decides)
    -- (its own shape first: the value's type when nothing else gives one)
    let fits := own :: fits.filter (· != own)
    out := out ++ [.classDef p s!"{n}$fn" [] [] (fits.map fun s => STy.app s.name targs) false [] [] methods]
  -- (#214) a value class per closed function type a value is asked for at
  -- and fits other than at its own types, `F$fn$k`, implementing that type's
  -- shape (and those with more effects) at the type's own arguments
  let variant (p : Pos) (n : String) (own : Shape) (k : Nat) (qs : List STy) (es : List String) (u : STy)
      (args : List SExpr) : Option STop :=
    let s := shapeOf qs.length es
    -- (the effects only: a tuple parameter may be flattened, #231)
    if !(shapeOf qs.length own.effs).within s then none else
    let fits := shapes.filter (s.within ·)
    let methods := fits.map fun s' =>
      STop.fn p s'.call (params qs) [] (s'.effs ++ ["override"]) u (.app p (.ident p n) args own.decides)
    let fits := s :: fits.filter (· != s)
    some (.classDef p s!"{n}$fn${k}" [] [] (fits.map fun s' => STy.app s'.name (qs ++ [u])) false [] [] methods)
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
  for (p, n, ps, effs, r) in values do
    let own := shapeOf ps.length effs
    let mut k := 0
    for (qs, es, u) in requested n do
      let some (ps', qs', args) := reshape p (ps.map (·.ty)) qs | continue
      let exact := qs.length == ps.length && ((ps.map (·.ty)).zip qs).all (fun (a, b) => reprStr (normS a) == reprStr (normS b)) &&
        reprStr (normS r) == reprStr (normS u)
      -- (contravariant parameters, a covariant result)
      if !exact && (qs'.zip ps').all (fun (a, b) => subAt anc a b) && subAt anc r u then
        if let some c := variant p n own k qs es u args then
          out := out ++ [c]
          k := k + 1
  for (p, n, ps, tps, effs, r) in gvalues do
    let own := shapeOf ps.length effs
    for a in genericAdapters p n (ps.map (·.ty)) tps r arities do
      let sh := shapeOf a.params.length effs
      let fits := shapes.filter (sh.within ·)
      let methods := fits.map fun s =>
        STop.fn p s.call (params a.params) [] (s.effs ++ ["override"]) a.ret
          (.app p (.ident p n) a.args own.decides)
      let fits := sh :: fits.filter (· != sh)
      out := out ++ [.classDef p s!"{n}$fn{a.suffix}" a.tparams []
        (fits.map fun s => STy.app s.name (a.params ++ [a.ret])) false [] [] methods]
    let tpn := tps.map (·.name)
    let mut k := 0
    for (qs, es, u) in requested n do
      let some (ps', qs', args) := reshape p (ps.map (·.ty)) qs | continue
      let θ := ((ps' ++ [r]).zip (qs' ++ [u])).foldlM (fun θ (a, b) => matchTy tpn θ a b) []
      if let some θ := θ then
        -- (every type parameter instantiated, a comparable one to a type
        -- that is surely comparable)
        if tps.all fun tp => match θ.lookup tp.name with
            | some t => tp.constraint != "comparable" || plainComparable t
            | none => false then
          if let some c := variant p n own k qs es u args then
            out := out ++ [c]
            k := k + 1
  for (p, c, ctps, mtps, m, ps, effs, r) in mvalues do
    let own := shapeOf ps.length effs
    let selfTy : STy := if ctps.isEmpty then .name c else .app c (ctps.map fun tp => .name tp.name)
    for a in genericAdapters p s!"{c}${m}" (ps.map (·.ty)) (ctps ++ mtps) r arities [selfTy] do
      let sh := shapeOf a.params.length effs
      let fits := shapes.filter (sh.within ·)
      let methods := fits.map fun s =>
        STop.fn p s.call (params a.params) [] (s.effs ++ ["override"]) a.ret
          (.app p (.member p (.ident p "$self") m) a.args own.decides)
      let fits := sh :: fits.filter (· != sh)
      out := out ++ [.classDef p s!"{c}${m}$fn{a.suffix}" a.tparams []
        (fits.map fun s => STy.app s.name (a.params ++ [a.ret])) false
        [("$self", selfTy.substNames a.subst, none, false)] [] methods]
    -- (#231) a method of a class without type parameters as a value at a
    -- closed function type it fits by variance, asked for as `.{c}${m}`:
    -- `{c}${m}$fn${k}`, holding the receiver
    if ctps.isEmpty && mtps.isEmpty then
      let args := (List.range ps.length).map fun i => SExpr.ident p s!"$X{i}"
      let mut k := 0
      for (qs, es, u) in requested s!".{c}${m}" do
        let exact := qs.length == ps.length && ((ps.map (·.ty)).zip qs).all (fun (a, b) => reprStr (normS a) == reprStr (normS b)) &&
          reprStr (normS r) == reprStr (normS u)
        let s := shapeOf qs.length es
        if !exact && qs.length == ps.length && own.within s &&
            (qs.zip (ps.map (·.ty))).all (fun (a, b) => subAt anc a b) && subAt anc r u then
          let vfits := shapes.filter (s.within ·)
          let vmethods := vfits.map fun s' =>
            STop.fn p s'.call (params qs) [] (s'.effs ++ ["override"]) u
              (.app p (.member p (.ident p "$self") m) args own.decides)
          let vfits := s :: vfits.filter (· != s)
          out := out ++ [.classDef p s!"{c}${m}$fn${k}" [] [] (vfits.map fun s' => STy.app s'.name (qs ++ [u])) false
            [("$self", .name c, none, false)] [] vmethods]
          k := k + 1
  return tops ++ out

end FnValues

end OpenVerse.Front
