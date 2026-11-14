/-
  OpenVerse front end — a type given as an argument and used as a type
  (Book of Verse tests: `FalseOption(t:type):?t = false`, then
  `FalseOption(int)`, ParametricTypes.versetest 613-624; `False(int) =
  False(logic)`, TypeParam.versetest 57-60; the design is in
  docs/research/types-as-values.md).

  A function's parameter `t:type` whose name the function uses as a type
  is a type parameter whose argument the call writes, and so is one
  `t:subtype(c)` or `t:castable_subtype(c)`, a bounded one (#502). The
  function is generic over `t` (`where t:type`, `where t:subtype(c)`), as if
  written so; the
  parameter, in its place, becomes `$typeArgument:t`, of type `?t`, which
  nothing reads; and a call's argument in its place, a type as written
  (`int`, `logic`, a class's or a struct's name, `c(int)`,
  `tuple(int, float)`), is the value `(?int)(false)` of that parameter, from
  which the call's type argument is inferred, as a generic call's are, with
  the type's witness (#520). No Verse Core is added.

  Refused: such an argument that is no type as written, and a type
  parameter given as one (`Foo(:t where t:type):void = Bar(t)`: the BPVM's
  link error, TypeParam.versetest:43; its VerseVM twin, :49, accepts it).
  A parameter `t:type` the function uses as a value (`F(X:type):type = X`)
  is a type value's, as `TypeValues` has it.
-/
import OpenVerse.Front.TypeValues

namespace OpenVerse.Front
namespace TypeArguments

/-- The prefix of the parameter a type argument becomes. -/
def paramPrefix : String := "$typeArgument:"

/-- The type an argument writes: a type's name, a parametric type applied
    (`c(int)`), `tuple(…)`; none for any other expression. -/
partial def writtenType? : SExpr → Option STy
  | .ident _ n => some (.name n)
  | .app _ (.ident _ "tuple") as false => (as.mapM writtenType?).map .tup
  | .app _ (.ident _ n) as false => (as.mapM writtenType?).map (.app n)
  | _ => none

/-- Whether a parameter's type makes it a type argument's: `type`, or a
    bound a type parameter may have, `subtype(c)`, `castable_subtype(c)`
    (#502; the Book's tests, `FORT-1059276.versetest:6`,
    `ParametricTypes.versetest` 1305-1329). -/
def typeArgumentKind : STy → Bool
  | .name "type" => true
  | .app k [_] => k == "subtype" || k == "castable_subtype"
  | _ => false

/-- The type parameter a type argument's parameter `v:k` is: `where v:type`,
    or bounded as its type says. -/
def typeParamOf (p : Pos) (v : String) : STy → TParam
  | .app "subtype" [a] => TParam.withUpperBound p v a
  | .app "castable_subtype" [a] => TParam.withMetatype p v "castable_subtype" a
  | _ => { pos := p, name := v, constraint := "type" }

/-- The positions of a function's parameters that are type arguments, with
    their names: `t:type` (or `t:subtype(c)`, `t:castable_subtype(c)`), not
    named, that the function uses as a type (in its other parameters' types,
    its result's, its type parameters' bounds or its body's declarations)
    and not as a value. -/
def typeArgumentsOf (ps : List SParam) (tps : List TParam) (r : STy) (b : SExpr) : List (Nat × String) :=
  let types : List STy := r :: ps.map (·.ty) ++ tps.filterMap (·.upperBound) ++ TypeValues.declTys b
  ps.zipIdx.filterMap fun (q, i) =>
    if !typeArgumentKind q.ty || q.named || q.default.isSome then none else
    let t := q.name
    if !types.any (·.mentions t) || (TypeValues.exprValues b).contains t then none else some (i, t)

/-- A call's arguments, those at type arguments' places written as their
    parameters' values; refused when one is no type, or a type parameter of
    the code that calls (`tps`). -/
def rewriteArgs (f : String) (places : List (Nat × String)) (tps : List String) (args : List SExpr) :
    Except String (List SExpr) := do
  -- (one argument per parameter, as written: a tuple for several is
  -- refused below, as it gives no type)
  args.zipIdx.mapM fun (a, i) => do
    let some (_, t) := places.find? (·.1 == i) | return a
    let some ty := writtenType? a
      | throw s!"{a.pos.show}: {f}'s parameter {t} is a type: write a type here, as int or c(int) (a type given as an argument)"
    if let .name n := ty then
      if tps.contains n then
        throw s!"{a.pos.show}: {n}, a type parameter, given as {f}'s type argument {t}: openverse takes the BPVM's reading, a link error (Book of Verse tests, TypeParam.versetest:43; VerseVM accepts it, :49)"
    return .app a.pos (.construct a.pos "$type" [.opt ty] []) [.ident a.pos "false"] false

/-- `e` with each call of a function with type arguments (`fns`) written
    with their parameters' values, in code whose type parameters are `tps`. -/
partial def rewriteCalls (fns : List (String × List (Nat × String))) (tps : List String) (e : SExpr) :
    Except String SExpr := do
  let e ← e.mapChildrenM (rewriteCalls fns tps)
  match e with
  -- (a call in brackets of a `<decides>` function too, `First[string, Xs]`)
  | .app p h@(.ident _ f) args bracket =>
    match fns.lookup f with
    | some places => return .app p h (← rewriteArgs f places tps args) bracket
    | none => return e
  | e => return e

/-- The program with its functions' type arguments written as type
    parameters and their calls' arguments as those parameters' values (the
    file's comment); unchanged when no function has one. -/
def desugar (tops : List STop) : Except String (List STop) := do
  -- the functions with type arguments, by name
  let fns : List (String × List (Nat × String)) := tops.filterMap fun
    | .fn _ n ps tps _ r b =>
      let places := typeArgumentsOf ps tps r b
      if places.isEmpty then none else some (n, places)
    | _ => none
  -- (a method's parameter `t:type` is not one: its calls are `X.M(…)`,
  -- which name no function the program writes)
  for t in tops do
    if let .classDef _ c _ _ _ _ _ _ ms := t then
      for m in ms do
        if let .fn mp mn ps mtps _ r b := m then
          if !(typeArgumentsOf ps mtps r b).isEmpty then
            throw s!"{mp.show}: {c}.{mn} takes a type as an argument (a parameter t:type used as a type): openverse takes types as arguments of functions only, not yet of methods"
  -- (a type argument comes before the parameters whose types use it, as a
  -- type parameter's scope begins at it: Book of Verse tests,
  -- SOL-4357-TypeType.versetest:28, 3502)
  for t in tops do
    if let .fn p n ps _ _ _ _ := t then
      for (i, v) in (fns.lookup n).getD [] do
        if let some q := (ps.take i).find? (·.ty.mentions v) then
          throw s!"{p.show}: {n}'s parameter {q.name} has a type that uses {v}, a type given as an argument after it: a type argument comes before the parameters whose types use it"
  if fns.isEmpty then return tops
  -- each call of one, in code whose type parameters are `tps`
  let rewrite := rewriteCalls fns
  let fn (t : STop) : Except String STop := do
    match t with
    | .fn p n ps tps specs r b =>
      let places := (fns.lookup n).getD []
      let tps' := tps ++ places.map fun (i, v) => typeParamOf p v (ps.getD i default).ty
      let ps' := ps.zipIdx.map fun (q, i) =>
        if places.any (·.1 == i) then { q with name := paramPrefix ++ q.name, ty := .opt (.name q.name) } else q
      let names := tps'.map (·.name)
      let ps' ← ps'.mapM fun q => do
        match q.default with
        | some d => return { q with default := some (← rewrite names d) }
        | none => return q
      return .fn p n ps' tps' specs r (← rewrite names b)
    | .const p n specs ty v => return .const p n specs ty (← rewrite [] v)
    | .classDef p n nsp tps specs parents isI fs ms =>
      let cvs := tps.map (·.name)
      let fs ← fs.mapM fun f => do
        match f.default with
        | some d => return { f with default := some (← rewrite cvs d) }
        | none => return f
      let ms ← ms.mapM fun
        | .fn mp mn ps mtps specs r b => do
          return .fn mp mn ps mtps specs r (← rewrite (cvs ++ mtps.map (·.name)) b)
        | m => pure m
      return .classDef p n nsp tps specs parents isI fs ms
  tops.mapM fn

end TypeArguments
end OpenVerse.Front
