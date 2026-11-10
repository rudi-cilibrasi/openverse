/-
  OpenVerse front end — casts that refine type arguments (#243), their
  surface side.

  In generic code, a cast `D := T[X]` whose class `T` fixes or repeats the
  type arguments of `X`'s class (`dup(t) := class(pair(t, t))`, with
  `X:pair(a, b)`) holds only under a refinement of the code's type
  parameters (`a = b`), which Verse Core gives a dispatch to classes with
  pins (`Typed.dispatch`), not a cast. So the branch it guards is lifted
  into a generic function, `$refine…(D, captured locals…)`, typed in the
  refined world, and the `if` becomes a dispatch to it:

      if (D := dup[P]) then Body else Else
        ⟶  if (P's class is dup) then $refine(P, X…) else Else

  The elaborator finds such a cast in a first elaboration and asks for the
  function (`Lift`); the program is then elaborated again with it, made
  here from the branch, with the refinement applied to the types written in
  it.
-/
import OpenVerse.Front.Choice

namespace OpenVerse.Front.Refine

/-- A refining cast's branch, lifted into a generic function (#243). -/
structure Lift where
  /-- The `if`'s position and the name its condition binds: the key. -/
  pos : Pos
  bound : String
  /-- The class cast to: it and the classes below it get pins in Verse
      Core, which the dispatch to the function refines by. -/
  target : String
  /-- The function made from the branch: its name, its parameters (the
      bound name first, then the locals the branch uses, each at its type
      under the refinement), type parameters, effects and result type. -/
  name : String
  params : List SParam
  tparams : List TParam
  specs : List String
  ret : STy
  /-- The refinement, on the enclosing function's type parameters, for the
      types written in the branch. -/
  subst : List (String × STy)
  /-- The type arguments the cast opens (#250), which `target` has and the
      object's type does not name: each type parameter of the function made
      for them, with the name of `target`'s type parameter it stands for,
      whose value it reads from the object's hidden field. -/
  opened : List (String × String) := []
  /-- The branch, when it is not taken from the source as written: in a
      method, with the members of `Self` it names bare made `Self.member`. -/
  body : Option SExpr := none
  /-- In a class's copy of an interface's default (#53): `$in` and the
      class, as the copies and the interface's own default share the
      source's places (`Ctx.liftTag`); such a lift always has its `body`. -/
  tag : String := ""
  deriving Inhabited

def keyOf (p : Pos) (bound : String) (tag : String := "") : String := s!"{p.file}:{p.line}:{p.col}:{bound}{tag}"

def Lift.key (l : Lift) : String := keyOf l.pos l.bound l.tag

/-- The sub-expressions of `e`, one level down. -/
def kids : SExpr → List SExpr
  | .str _ ps => ps.filterMap fun | .code c => some c | _ => none
  | .app _ g as _ => g :: as
  | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
  | .gen _ _ _ x | .decl _ _ _ _ x => [x]
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => [a, b]
  | .cmp _ a r => a :: r.map (·.2)
  | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es
  | .ite _ cs t e' => cs ++ [t] ++ e'.toList
  | .forE _ cs b => cs ++ [b]
  | .ret _ x => x.toList
  | .caseE _ sc arms => sc :: arms.flatMap fun (pt, v) => pt.toList ++ [v]
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => [k, v]
  | _ => []

/-- Whether `pr` holds of `e` or a part of it outside the `loop`s in it. -/
partial def anyOutsideLoops (pr : SExpr → Bool) (e : SExpr) : Bool :=
  pr e || match e with
    | .loop .. => false
    | e => (kids e).any (anyOutsideLoops pr)

/-- The first part of `e` (outside its `loop`s, if `outside`) for which
    `pr` holds. -/
partial def findPart (pr : SExpr → Bool) (outside : Bool) (e : SExpr) : Option SExpr :=
  if pr e then some e
  else match e with
    | .loop .. => if outside then none else (kids e).findSome? (findPart pr outside)
    | e => (kids e).findSome? (findPart pr outside)

/-- The names in a written type. -/
partial def styNames : STy → List String
  | .name n => [n]
  | .arr t | .opt t => styNames t
  | .tup ts => ts.flatMap styNames
  | .map k v => styNames k ++ styNames v
  | .app n ts => n :: ts.flatMap styNames
  | .fn ps _ r => ps.flatMap styNames ++ styNames r

/-- The type names written in `e` (in declarations and constructions). -/
partial def typeNames (e : SExpr) : List String :=
  let own : List String := match e with
    | .decl _ _ (some t) _ _ => styNames t
    | .construct _ _ ts _ => ts.flatMap styNames
    | _ => []
  own ++ (kids e).flatMap typeNames

/-- `e` with the type names in `σ` substituted in the types written in it
    (declarations, constructions). -/
partial def substTypes (σ : List (String × STy)) : SExpr → SExpr :=
  Choice.mapE fun
    | .decl p n (some t) v x => some (.decl p n (some (t.substNames σ)) v (substTypes σ x))
    | .construct p n ts fs => some (.construct p n (ts.map (·.substNames σ)) (fs.map (substTypes σ)))
    | _ => none

/-- The branch of a refining cast that is the first clause of an `if`'s
    condition, `if (D := T[X], rest) then B else E`: the `if` of the rest,
    `if (rest, true?) then B else E` (the cast has no effects to undo when
    the rest fails; `true?`, which may fail, keeps the rest a condition
    when it cannot fail itself, as the whole condition could). -/
def castRest (p : Pos) (more : List SExpr) (body : SExpr) (els : Option SExpr) : SExpr :=
  if more.isEmpty then body else .ite p (more ++ [.query p (.ident p "true")]) body els

/-- The branches the lifts ask for, as functions: each `if (D := …) then
    Body …` whose position and bound name are a lift's key gives `Body`,
    with the refinement applied to its written types. Found anywhere in the
    program, also in a branch that is lifted itself. -/
def functions (lifts : List Lift) (tops : List STop) : List STop := Id.run do
  if lifts.isEmpty then return []
  let mut out : Array STop := #[]
  let mut done : List String := []
  -- (a branch the lift has, a method's or one the elaborator made, as it is)
  for l in lifts do
    if let some b := l.body then
      done := l.key :: done
      out := out.push (.fn l.pos l.name l.params l.tparams l.specs l.ret (substTypes l.subst b))
  let mut todo : List SExpr := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
    | .classDef _ _ _ _ _ _ _ _ ms => ms.flatMap fun
        | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
        | _ => []
    | _ => []
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    if let .ite p [.decl _ d none false _] body _ := e then
      if let some l := lifts.find? (·.key == keyOf p d) then
        if !done.contains l.key then
          done := l.key :: done
          out := out.push (.fn p l.name l.params l.tparams l.specs l.ret (substTypes l.subst body))
    todo := kids e ++ todo
  return out.toList

end OpenVerse.Front.Refine
