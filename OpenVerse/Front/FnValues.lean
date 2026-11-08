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

/-- Whether a type mentions the type name `x`. -/
partial def _root_.OpenVerse.Front.STy.hasName (x : String) : STy → Bool
  | .name n => n == x
  | .arr t | .opt t => t.hasName x
  | .tup ts | .app _ ts => ts.any (·.hasName x)
  | .map a b => a.hasName x || b.hasName x
  | .fn ps _ r => ps.any (·.hasName x) || r.hasName x

/-- The type names a type mentions. -/
partial def _root_.OpenVerse.Front.STy.allNames : STy → List String
  | .name n => [n]
  | .arr t | .opt t => t.allNames
  | .tup ts => ts.flatMap STy.allNames
  | .app n ts => n :: ts.flatMap STy.allNames
  | .map a b => a.allNames ++ b.allNames
  | .fn ps _ r => ps.flatMap STy.allNames ++ r.allNames

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
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b => scanL [a, b]
  | .cmp _ a rest => scanL (a :: rest.map (·.2))
  | .tuple _ es | .block _ es | .arrayLit _ es => scanL es
  | .ite _ cs t e => scanL (cs ++ [t] ++ e.toList)
  | .forE _ cs b =>
    -- (a generator's names are bound there: `for (Double : Xs)` means them)
    let bound := cs.flatMap fun | .gen _ x i _ => x :: i.toList | _ => []
    let (s, n) := scanL (cs ++ [b])
    (s, n.filter (!bound.contains ·))
  | .ret _ e => scanL e.toList
  | .caseE _ e arms => scanL (e :: arms.flatMap fun (pat, v) => pat.toList ++ [v])
  | .decl _ _ t _ e =>
    let (s, n) := e.scan
    ((t.map STy.fnShapes).getD [] ++ s, n)
  | .set _ l _ e => scanL [l, e]
  | .structDef _ _ fs =>
    let (s, n) := scanL (fs.filterMap (·.2.2.1))
    (fs.flatMap (·.2.1.fnShapes) ++ s, n)
  | .refineDef _ _ t cs =>
    let (s, n) := scanL cs
    (t.fnShapes ++ s, n)
  | .construct _ _ ts args =>
    let (s, n) := scanL args
    (ts.flatMap STy.fnShapes ++ s, n)
  | .mapLit _ kvs => scanL (kvs.flatMap fun (k, v) => [k, v])
  | .str _ parts => scanL (parts.filterMap fun | .code e => some e | .text _ => none)
  | _ => ([], [])
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

/-- `a` is `b` or a subtype the elaborator converts at a parameter or a
    result (#214): `int` to `rational`, a class to one above it. Nothing
    else, so a value class made for a function type always elaborates. -/
def subAt (anc : String → List String) (a b : STy) : Bool :=
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
  -- (a method value's class is valid when the class's type parameters
  -- occur once each in the shape's type arguments, as whole types)
  let valid (tps : List TParam) (targs : List STy) : Bool :=
    let tpn := tps.map (·.name)
    let bare := targs.filterMap fun | .name x => if tpn.contains x then some x else none | _ => none
    let whole := targs.all fun t => match t with
      | .name _ => true
      | t => !tpn.any t.hasName
    whole && tpn.all bare.contains && bare.eraseDups.length == bare.length
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
  let mvalues : List (Pos × String × List TParam × String × List SParam × List String × STy) :=
    tops.flatMap fun
      | .classDef _ c tps _ _ _ _ _ ms => ms.filterMap fun
        | .fn mp m ps mtps effs r _ =>
          let targs := ps.map (·.ty) ++ [r]
          -- (an override needs a class of its own only when its type is not
          -- its declaration's, a narrower result, #219, or the declaration's
          -- class cannot have one, as a generic interface's method that a
          -- class implements at closed types: otherwise the declaration's
          -- value dispatches to it, and one class per override in a long
          -- chain of them makes code without end)
          let needed := !effs.contains "override" || match declOf (tops.length + 1) c m with
            | some (dtps, dtargs) =>
              !(valid dtps dtargs) || dtargs.length != targs.length ||
                (dtargs.zip targs).any fun (a, b) => reprStr a != reprStr b
            | none => true
          let tpn := tps.map (·.name)
          -- (a class's type parameters only as whole, distinct type
          -- arguments of the shape: a class that repeats or nests them
          -- could not implement it, #171)
          let bare := targs.filterMap fun | .name x => if tpn.contains x then some x else none | _ => none
          let whole := targs.all fun t => match t with
            | .name _ => true
            | t => !tpn.any t.hasName
          let overloaded := (ms.filter fun | .fn _ m' .. => m' == m | _ => false).length > 1
          -- (and every one of them: the class's type arguments must be
          -- recoverable from the shape's, #53)
          let complete := tpn.all bare.contains
          if members.contains m && needed && !overloaded && mtps.isEmpty && ps.all (!·.named) && !m.contains '$' &&
              !m.startsWith "(" &&
              whole && complete && bare.eraseDups.length == bare.length then
            some (mp, c, tps, m, ps, effs, r)
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
      mvalues.map (fun (_, _, _, _, ps, effs, _) => shapeOf ps.length effs) do
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
  let variant (p : Pos) (n : String) (own : Shape) (k : Nat) (qs : List STy) (es : List String) (u : STy) :
      Option STop :=
    let s := shapeOf qs.length es
    if !own.within s then none else
    let fits := shapes.filter (s.within ·)
    let args := (List.range qs.length).map fun i => SExpr.ident p s!"$X{i}"
    let methods := fits.map fun s' =>
      STop.fn p s'.call (params qs) [] (s'.effs ++ ["override"]) u (.app p (.ident p n) args own.decides)
    let fits := s :: fits.filter (· != s)
    some (.classDef p s!"{n}$fn${k}" [] [] (fits.map fun s' => STy.app s'.name (qs ++ [u])) false [] [] methods)
  for (p, n, ps, effs, r) in values do
    let own := shapeOf ps.length effs
    let mut k := 0
    for (qs, es, u) in requested n do
      let exact := qs.length == ps.length && ((ps.map (·.ty)).zip qs).all (fun (a, b) => reprStr a == reprStr b) &&
        reprStr r == reprStr u
      -- (contravariant parameters, a covariant result)
      if !exact && qs.length == ps.length && (qs.zip (ps.map (·.ty))).all (fun (a, b) => subAt anc a b) &&
          subAt anc r u then
        if let some c := variant p n own k qs es u then
          out := out ++ [c]
          k := k + 1
  for (p, n, ps, tps, effs, r) in gvalues do
    let own := shapeOf ps.length effs
    let tpn := tps.map (·.name)
    let mut k := 0
    for (qs, es, u) in requested n do
      if qs.length != ps.length then continue
      let θ := ((ps.map (·.ty) ++ [r]).zip (qs ++ [u])).foldlM (fun θ (a, b) => matchTy tpn θ a b) []
      if let some θ := θ then
        -- (every type parameter instantiated, a comparable one to a type
        -- that is surely comparable)
        if tps.all fun tp => match θ.lookup tp.name with
            | some t => tp.constraint != "comparable" || plainComparable t
            | none => false then
          if let some c := variant p n own k qs es u then
            out := out ++ [c]
            k := k + 1
  for (p, c, ctps, m, ps, effs, r) in mvalues do
    let own := shapeOf ps.length effs
    let fits := shapes.filter (own.within ·)
    let targs := ps.map (·.ty) ++ [r]
    let args := (List.range ps.length).map fun i => SExpr.ident p s!"$X{i}"
    let selfTy : STy := if ctps.isEmpty then .name c else .app c (ctps.map fun tp => .name tp.name)
    let methods := fits.map fun s =>
      STop.fn p s.call (params (ps.map (·.ty))) [] (s.effs ++ ["override"]) r
        (.app p (.member p (.ident p "$self") m) args own.decides)
    let fits := own :: fits.filter (· != own)
    out := out ++ [.classDef p s!"{c}${m}$fn" ctps [] (fits.map fun s => STy.app s.name targs) false
      [("$self", selfTy, none, false)] [] methods]
  return tops ++ out

end FnValues

end OpenVerse.Front
