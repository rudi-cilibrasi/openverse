/- The built-in functions: what each takes, and how a call of it is elaborated. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse

/-- What a built-in function takes, as its refusals say it. -/
inductive Arity where
  /-- exactly `n` -/
  | exactly (n : Nat)
  /-- one or two -/
  | oneOrTwo
  /-- any number -/
  | any

/-- Whether a call with `n` arguments has the number the arity says. -/
def Arity.admits (n : Nat) : Arity → Bool
  | .exactly k => n == k
  | .oneOrTwo => n == 1 || n == 2
  | .any => true

/-- `Arity.show "float"`: "one float", "two floats", "one or two floats". -/
def Arity.show (noun : String) : Arity → String
  | .exactly n =>
    let word := match n with
      | 0 => "no" | 1 => "one" | 2 => "two" | 3 => "three" | n => toString n
    s!"{word} {noun}{if n == 1 then "" else "s"}"
  | .oneOrTwo => s!"one or two {noun}s"
  | .any => s!"any number of {noun}s"

/-- A call of a built-in function, as its elaboration takes it: the
    expression elaborator's entry points it calls back into, the call's
    context and place, the built-in's name and arity, and the call's
    arguments and brackets as written. -/
structure BuiltinCall where
  elabE : Ctx → SExpr → Option Ty → EM R
  elabArgs : Ctx → Pos → List SExpr → List Ty → EM (List Expr)
  elabInts : Ctx → Pos → List SExpr → EM (List Expr)
  ctx : Ctx
  p : Pos
  name : String
  arity : Arity
  args : List SExpr
  bracket : Bool
  exp : Option Ty

/-- A built-in function: its name, what it takes, and how a call of it is
    elaborated. -/
structure Builtin where
  name : String
  arity : Arity
  elaborate : BuiltinCall → EM R

namespace BuiltinCall

/-- The refusal of a call with other arguments than the built-in takes,
    `Abs takes one argument`, `Pow takes two floats`. -/
def wrongArity (c : BuiltinCall) (noun : String) : EM α :=
  eerr c.p s!"{c.name} takes {c.arity.show noun}"

/-- A built-in that can fail is called `F[…]` (Book of Verse §8.1). -/
def needBracket (c : BuiltinCall) : EM Unit := do
  if !c.bracket then eerr c.p s!"{c.name} can fail: call it with {c.name}[…]"

/-- A built-in that cannot fail is called `F(…)`. -/
def noBracket (c : BuiltinCall) : EM Unit := do
  if c.bracket then eerr c.p s!"{c.name} cannot fail: call it with {c.name}(…)"

end BuiltinCall

/-- `Concatenate(A, B, …)` (#150): an array of arrays flattened, or several
    arrays one after the other (as a tuple of them converts to an array of
    arrays); `Concatenate()`, the empty array of the expected type. -/
partial def elabConcatenate (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, args, exp, .. } := c
  match args with
  | [] => match exp with
    | some (.arr t) => return ⟨.lit Value.emptyArray, .arr t⟩
    | _ => eerr p "Concatenate() needs an expected array type"
  | [a] =>
    let r ← elabE ctx a (match exp with | some t => some (.arr t) | none => none)
    let r ← elabArrayArgumentWith elabE ctx a.pos r 2 "Concatenate"
    match r.ty with
    | .arr (.arr t) =>
      -- (through a typed temporary: an empty literal has no type of its own)
      let tv ← fresh r.ty
      return ⟨.seq (.assign tv r.e) (.prim .flatten [.local tv]), .arr t⟩
    | t => eerr p s!"Concatenate takes arrays, or an array of arrays, found {t.show}"
  | a :: rest =>
    let r0 ← elabE ctx a exp
    let r0 ← elabArrayArgumentWith elabE ctx a.pos r0 1 "Concatenate"
    let .arr t := r0.ty | eerr a.pos s!"Concatenate takes arrays, found {r0.ty.show}"
    let mut acc := r0.e
    for b in rest do
      let rb ← elabE ctx b (some (.arr t))
      acc := p2 .concat acc (← elabArgumentCoerceWith elabE ctx b.pos rb (.arr t))
    return ⟨acc, .arr t⟩

/-- `any(X)`: `X` as an `any` (#138), evaluated. -/
def elabAnyValue (c : BuiltinCall) : EM R := do
  let [a] := c.args | eerr c.p "any(…) takes one value"
  let r ← c.elabE c.ctx a none
  return ⟨← coerce a.pos r .any, .any⟩

/-- `comparable(X)`: `X` boxed as a `comparable` (Book of Verse ch. 11,
    `comparable(15) = comparable(15)`). -/
def elabComparableValue (c : BuiltinCall) : EM R := do
  let [a] := c.args | eerr c.p "comparable(…) takes one value"
  let r ← c.elabE c.ctx a none
  if !isComparable c.ctx.types r.ty then
    eerr a.pos (notComparable c.ctx.types r.ty "the value of comparable(…)")
  return ⟨← coerce a.pos r .dyn, .dyn⟩

/-- `Print(S)`: the string `S` printed, then a new line. -/
def elabPrint (c : BuiltinCall) : EM R := do
  let es ← c.elabArgs c.ctx c.p c.args [Ty.string]
  return ⟨.print es.head!, .void⟩

/-- `ConcatenateMaps(A, B)`: the entries of every map laid down in turn, a
    later map's pair replacing an earlier one's of its key, at its own place
    (the Book of Verse's API reference: "the entries are laid down left
    first, then right, and a map keeps only the last value given for a
    key"; `Tests/Intrinsics/ConcatenateMaps.versetest` 21, 33: the later
    map's order): the first copied, then for each other the pairs kept whose
    key it does not have, then its pairs. Two maps, the Book of Verse's
    ch. 3: "It takes exactly two maps"; more are merged by chained calls. -/
partial def elabConcatenateMaps (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, args, exp, .. } := c
  if args.length != 2 then
    eerr p s!"{c.name} takes {c.arity.show "map"}, not {args.length} (to merge more, chain the calls: ConcatenateMaps(ConcatenateMaps(A, B), C))"
  let some a0 := args.head? | eerr p "ConcatenateMaps takes two maps"
  -- the maps' type: the expected one, else the first argument's that has
  -- one alone (an empty map{} has none)
  let mapExp : Option Ty ← match exp with
    | some t@(.map ..) => pure (some t)
    | _ =>
      let st ← get
      let mut found : Option Ty := none
      for a in args do
        if found.isNone then
          found ← tryCatch (do
            let r ← elabE ctx a none
            let r ← elabContainerReceiverWith elabE ctx a.pos r (fun | .map .. => true | _ => false) "ConcatenateMaps"
            pure (match r.ty with | t@(.map ..) => some t | _ => none))
            (fun _ => pure none)
      set st
      pure found
  let mut rs : Array R := #[]
  let mut jt? : Option Ty := none
  for a in args do
    let r ← elabE ctx a mapExp
    let r ← elabContainerReceiverWith elabE ctx a.pos r (fun | .map .. => true | _ => false) "ConcatenateMaps"
    let .map _ _ := r.ty | eerr a.pos s!"ConcatenateMaps takes maps, not {r.ty.show}"
    match jt? with
    | none => jt? := some r.ty
    | some j =>
      let j' ← tryCatch (join a.pos j r.ty mapExp) (fun _ =>
        match SubtypeEvidence.joinView? ctx.types ctx.evidenceTypes [j, r.ty] mapExp with
        | some target => pure target
        | none => eerr a.pos s!"ConcatenateMaps takes maps of one type, not {j.show} and {r.ty.show}")
      jt? := some j'
    rs := rs.push r
  let some jt := jt? | eerr p "ConcatenateMaps takes at least one map"
  let .map kt vt := jt | eerr p s!"ConcatenateMaps takes maps, not {jt.show}"
  let tm ← fresh jt
  let some r0 := rs[0]? | eerr p "ConcatenateMaps takes at least one map"
  let mut code : Expr := .assign tm (← elabArgumentCoerceWith elabE ctx a0.pos r0 jt)
  for (r, a) in rs.toList.tail.zip args.tail do
    let ts ← fresh jt
    let tpair ← fresh (.tup [kt, vt])
    let tk ← fresh kt
    let tq ← fresh (.tup [kt, vt])
    -- (a pair stays, at its place, when the later map has no pair of its key)
    let absent := Expr.notE (.seq (.assign tk (.prim (.tupGet 0) [.local tpair])) (mapLookup ts tk tq))
    let kept := Expr.forE tpair (.local tm) absent (.local tpair)
    code := .seq code (.seq (.assign ts (← elabArgumentCoerceWith elabE ctx a.pos r jt))
      (.assign tm (.prim .concat [kept, .local ts])))
  return ⟨.seq code (.local tm), jt⟩

/-- `ToString(X)`: the string of an int, a float, a char or a string. -/
def elabToString (c : BuiltinCall) : EM R := do
  match c.args with
  | [a] => return ⟨← elabToStringWith c.elabE c.ctx c.p (← c.elabE c.ctx a none), Ty.string⟩
  | _ => c.wrongArity "argument"

/-- `Abs(X)`: of an int, or of a float (#127); the argument elaborated once. -/
def elabAbs (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, name, args, .. } := c
  match args with
  | [a] =>
    let r := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p (← elabE ctx a none) name)
    if r.ty == .float then return ⟨.prim .fabs [r.e], .float⟩
    return ⟨.prim .abs [← coerce a.pos r .int], .int⟩
  | _ => c.wrongArity "argument"

/-- A call of a mathematical function of floats (#132): one that can fail
    (`IsFinite`) is called `F[…]`, the others `F(…)`; those the API declares
    `<reads>` (`Sinh` and its kin, `Lerp`) have that effect. Then `body`,
    given the function that elaborates an argument as a float, gives the
    call, or `none` when it has other arguments than the function takes. -/
def elabFloatFunction (fails reads : Bool)
    (body : BuiltinCall → (SExpr → EM Expr) → EM (Option R)) (c : BuiltinCall) : EM R := do
  if fails then c.needBracket
  else c.noBracket
  if reads then noteFx c.p ["reads"] (some c.name)
  let fl (a : SExpr) : EM Expr := do
    let r := widenR c.ctx.types (← c.elabE c.ctx a (some .float))
    if r.ty != .float then eerr a.pos s!"{c.name} takes floats, found {r.ty.show}"
    return r.e
  match ← body c fl with
  | some r => return r
  | none => c.wrongArity "float"

/-- `F(X)`: a function of one float that is a primitive of Verse Core,
    `Sqrt(X)`, `IsFinite[X]`. -/
def floatUnary (op : Prim) (fails : Bool := false) (reads : Bool := false) : BuiltinCall → EM R :=
  elabFloatFunction fails reads fun c fl => do
    let [a] := c.args | return none
    return some ⟨.prim op [← fl a], .float⟩

/-- `Pow(X, Y)`: `X` to the power `Y`. -/
def elabPow : BuiltinCall → EM R :=
  elabFloatFunction false false fun c fl => do
    let [a, b] := c.args | return none
    return some ⟨p2 .fpow (← fl a) (← fl b), .float⟩

/-- `ArcTan(X)`, and `ArcTan(Y, X)`, the angle of the point `(X, Y)`. -/
def elabArcTan : BuiltinCall → EM R :=
  elabFloatFunction false false fun c fl => do
    match c.args with
    | [y, x] => return some ⟨p2 .fatan2 (← fl y) (← fl x), .float⟩
    | [a] => return some ⟨.prim .fatan [← fl a], .float⟩
    | _ => return none

/-- `Log(Base, X)`: `Ln(X) / Ln(Base)`, the base evaluated first. -/
def elabLog : BuiltinCall → EM R :=
  elabFloatFunction false false fun c fl => do
    let [b, x] := c.args | return none
    let tb ← fresh .float
    let eb ← fl b
    let ex ← fl x
    return some ⟨.seq (.assign tb eb) (p2 .fdiv (.prim .fln [ex]) (.prim .fln [.local tb])), .float⟩

/-- `Lerp(A, B, T)`: `A * (1 - T) + B * T`, each argument evaluated once, in
    order. -/
def elabLerp : BuiltinCall → EM R :=
  elabFloatFunction false true fun c fl => do
    let [a, b, parameter] := c.args | return none
    let ta ← fresh .float
    let ea ← fl a
    let tb ← fresh .float
    let eb ← fl b
    let tp ← fresh .float
    let ep ← fl parameter
    let one := Expr.lit (.float 0x3FF0000000000000)
    let blend := p2 .fadd (p2 .fmul (.local ta) (p2 .fsub one (.local tp)))
      (p2 .fmul (.local tb) (.local tp))
    return some ⟨.seq (.assign ta ea) (.seq (.assign tb eb) (.seq (.assign tp ep) blend)), .float⟩

/-- `Round[X]`, `Int[X]`: a float to an int (#127), `Round` to the nearest,
    ties to even, `Int` towards zero; failing on NaN, an infinity or out of
    range. -/
def floatToInt (op : Prim) (c : BuiltinCall) : EM R := do
  c.needBracket
  match c.args with
  | [a] =>
    let r := widenR c.ctx.types (← c.elabE c.ctx a (some .float))
    if r.ty != .float then eerr c.p s!"{c.name} takes a float, found {r.ty.show}"
    return ⟨.prim op [r.e], .int⟩
  | _ => c.wrongArity "argument"

/-- `Floor`, `Ceil` (`up`): of a float (#127), failable, so with brackets;
    of a rational or an int, with either, as the Book writes both (of a
    rational, #116, never failing: its denominator is positive; of an int,
    the int); `Floor(X / Y)` of ints or rationals rounds their quotient. -/
def elabFloorCeil (up : Bool) (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, name, args, bracket, .. } := c
  let ofFloat (r : R) : EM R := do
    if !bracket then eerr p s!"{name} of a float can fail: call it with {name}[…]"
    return ⟨.prim (if up then .fceil else .ffloor) [r.e], .int⟩
  match args with
  | [.bin bp "/" a b] =>
    let ra := widenR ctx.types (← elabArithmeticOperandWith elabE ctx bp (← elabE ctx a none) name)
    let rb := widenR ctx.types (← elabArithmeticOperandWith elabE ctx bp
      (← elabE ctx b (if ra.ty == .float then some .float else none)) name)
    if ra.ty == .float && rb.ty == .float then return ← ofFloat ⟨p2 .fdiv ra.e rb.e, .float⟩
    if ra.ty == .float || rb.ty == .float then
      eerr bp s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
    if ra.ty == .rational || rb.ty == .rational then
      return ⟨← roundRational up (← rationalBinary bp .quotient ra rb), .int⟩
    let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
    return ⟨.prim (if up then .ceilDiv else .floorDiv) es, .int⟩
  | [e] =>
    let r := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p (← elabE ctx e none) name)
    match r.ty with
    | .int => return r
    | .float => ofFloat r
    | .rational =>
      return ⟨← roundRational up r.e, .int⟩
    | t => eerr p s!"{name} takes a rational or an int, found {t.show}"
  | _ => c.wrongArity "argument"

/-- `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean): a primitive of ints that can
    fail (when `Y` is 0). The number of arguments is not checked here:
    `elabInts` takes as many as are written. -/
def failableInts (op : Prim) (c : BuiltinCall) : EM R := do
  c.needBracket
  return ⟨.prim op (← c.elabInts c.ctx c.p c.args), .int⟩

/-- `Min(X, Y)`, `Max(X, Y)` (`isMin`): of two ints, or of two floats
    (#127: NaN when either is); each argument elaborated once. -/
def elabMinMax (isMin : Bool) (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, name, args, .. } := c
  let [a, b] := args | c.wrongArity "argument"
  let ra := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p (← elabE ctx a none) name)
  let rb := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p
    (← elabE ctx b (if ra.ty == .float || ra.ty == .int then some ra.ty else none)) name)
  if ra.ty == .float then
    if rb.ty != .float then eerr p s!"{name} takes two floats or two ints, found float and {rb.ty.show}"
    return ⟨p2 (if isMin then .fmin else .fmax) ra.e rb.e, .float⟩
  let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
  let ta ← fresh .int
  let tb ← fresh .int
  let op := if isMin then Prim.le else Prim.ge
  return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
    (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩

/-- `Clamp(Val, A, B)` and `Sgn(X)` (the Book's Runtime API and Epic's):
    `Clamp`, the median of the three, so the order of `A` and `B` does not
    matter, of ints or of floats, among which NaN orders above +Inf; `Sgn`,
    -1, 0 or 1 of an int or a float, NaN of NaN; each argument evaluated
    once, in order, the first deciding whether the call is of floats. -/
def elabClampOrSgn (c : BuiltinCall) : EM R := do
  let { elabE, ctx, p, name, args, .. } := c
  c.noBracket
  let some a0 := args.head? | c.wrongArity "argument"
  let r0 := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p (← elabE ctx a0 none) name)
  let isF := r0.ty == .float
  let t : Ty := if isF then .float else .int
  let operand (a : SExpr) (r : R) : EM Expr := do
    if isF then
      if r.ty != .float then eerr a.pos s!"{name} takes floats or ints, found float and {r.ty.show}"
      return r.e
    coerce a.pos r .int
  let lit (i : Int) : Expr := .lit (if isF then .float (VFloat.canon (Float.ofInt i)) else .int i)
  let ta ← fresh t
  let ea ← operand a0 r0
  match name, args with
  | "Sgn", [_] =>
    let (above, below) := if isF then (Prim.fgt, Prim.flt) else (Prim.gt, Prim.lt)
    -- (NaN, and zero, are their own sign)
    return ⟨.seq (.assign ta ea) (.ite (p2 above (.local ta) (lit 0)) (lit 1)
      (.ite (p2 below (.local ta) (lit 0)) (lit (-1)) (.local ta))), t⟩
  | "Clamp", [_, a, b] =>
    let ra := widenR ctx.types (← elabE ctx a (some t))
    let tb ← fresh t
    let ea' ← operand a ra
    let rb := widenR ctx.types (← elabE ctx b (some t))
    let tc ← fresh t
    let eb ← operand b rb
    -- `X ≤ Y`, NaN above every float: X ≤ Y (Verse Core's `fle`, which
    -- holds of a NaN and itself), or Y is NaN (not ≤ +Inf)
    let le (x y : Nat) : Expr :=
      if isF then .ite (p2 .fle (.local x) (.local y)) (.local x)
        (.ite (p2 .fle (.local y) (.lit (.float 0x7FF0000000000000))) (.prim .fail []) (.local x))
      else p2 .le (.local x) (.local y)
    let (lo, hi, m) := (← fresh t, ← fresh t, ← fresh t)
    let pick (cond : Expr) (x y : Nat) : Expr := .ite cond (.local x) (.local y)
    return ⟨.seq (.assign ta ea) (.seq (.assign tb ea') (.seq (.assign tc eb)
      (.seq (.assign lo (pick (le tb tc) tb tc)) (.seq (.assign hi (pick (le tb tc) tc tb))
      (.seq (.assign m (pick (le ta hi) ta hi)) (pick (le lo m) m lo)))))), t⟩
  | _, _ => c.wrongArity "argument"

/-- A bitwise function (the Book's ch. 4 and API): of ints, as two's
    complement sign-extended without limit, a result out of the int range
    the overflow error; the shifts (`shift`) fail on a negative count, so
    they are called `F[…]`. `BitNot(X)` is `-1 - X`; the others call helpers
    written in Verse (`Front/Bitwise.lean`), each argument evaluated once, in
    order. -/
def elabBitwise (shift : Bool) (c : BuiltinCall) : EM R := do
  if shift then c.needBracket else c.noBracket
  if !c.arity.admits c.args.length then
    eerr c.p s!"{c.name} takes {c.arity.show "int"}, found {c.args.length} argument(s)"
  let es ← c.elabInts c.ctx c.p c.args
  if c.name == "BitNot" then return ⟨.prim .sub [.lit (.int (-1)), es[0]!], .int⟩
  let helper := "$bit" ++ (c.name.drop 3).toString
  let some s := c.ctx.sig? helper | eerr c.p s!"internal error: the bitwise helper {helper} is missing"
  return ⟨.call s.idx es, .int⟩

/-- `Err()`: the program stops with an error; its value is of every type.
    The first place it is called is noted (`errAt`). Its arguments, if any
    are written, are not looked at. -/
def elabErr (c : BuiltinCall) : EM R := do
  modify fun st => if st.errAt.isNone then { st with errAt := some c.p } else st
  return ⟨.prim .userErr [], .never⟩

/-- `$Show(X)`, the entry of `openverse run FILE do EXPR`: the value printed
    when it has a `ToString`, else just evaluated. -/
def elabShow (c : BuiltinCall) : EM R := do
  match c.args with
  | [a] =>
    let r := widenR c.ctx.types (← elabPrintableValueWith c.elabE c.ctx c.p (← c.elabE c.ctx a none))
    match r.ty with
    | .int | .char | .char32 | .float | .arr .char => return ⟨.print (← toStringOf c.p r), .void⟩
    | _ => return ⟨← discardValue r, .void⟩
  | _ => eerr c.p "internal: $Show"

/-- The built-in functions: each one's name, what it takes, and how a call
    of it is elaborated. A call of one is the row of its name
    (`builtinCalled` says which name a call means), tried after the
    program's own kinds of names and before its functions
    (`elabAppBaseWith`).

    To add a built-in function: a row here, with its elaboration above (a
    function of the `BuiltinCall`, which says its arity in its refusals with
    `wrongArity`), and its name in `builtins` (no program may define a
    function of the name) or `softBuiltins` (a program's own definition is
    the one a call means), `Elab/Context.lean`. Every row's name is in one
    of them but `any` and `comparable`, which name types, and the entry
    `$Show`. -/
def builtinFunctions : List Builtin := [
  ⟨"Concatenate", .any, elabConcatenate⟩,
  ⟨"any", .exactly 1, elabAnyValue⟩,
  ⟨"comparable", .exactly 1, elabComparableValue⟩,
  ⟨"Print", .exactly 1, elabPrint⟩,
  ⟨"ConcatenateMaps", .exactly 2, elabConcatenateMaps⟩,
  ⟨"ToString", .exactly 1, elabToString⟩,
  ⟨"Abs", .exactly 1, elabAbs⟩,
  ⟨"Sqrt", .exactly 1, floatUnary .fsqrt⟩,
  ⟨"Exp", .exactly 1, floatUnary .fexp⟩,
  ⟨"Ln", .exactly 1, floatUnary .fln⟩,
  ⟨"Log", .exactly 2, elabLog⟩,
  ⟨"Pow", .exactly 2, elabPow⟩,
  ⟨"Sin", .exactly 1, floatUnary .fsin⟩,
  ⟨"Cos", .exactly 1, floatUnary .fcos⟩,
  ⟨"Tan", .exactly 1, floatUnary .ftan⟩,
  ⟨"ArcSin", .exactly 1, floatUnary .fasin⟩,
  ⟨"ArcCos", .exactly 1, floatUnary .facos⟩,
  ⟨"ArcTan", .oneOrTwo, elabArcTan⟩,
  ⟨"IsFinite", .exactly 1, floatUnary .fisFinite (fails := true)⟩,
  ⟨"Sinh", .exactly 1, floatUnary .fsinh (reads := true)⟩,
  ⟨"Cosh", .exactly 1, floatUnary .fcosh (reads := true)⟩,
  ⟨"Tanh", .exactly 1, floatUnary .ftanh (reads := true)⟩,
  ⟨"ArSinh", .exactly 1, floatUnary .fasinh (reads := true)⟩,
  ⟨"ArCosh", .exactly 1, floatUnary .facosh (reads := true)⟩,
  ⟨"ArTanh", .exactly 1, floatUnary .fatanh (reads := true)⟩,
  ⟨"Lerp", .exactly 3, elabLerp⟩,
  ⟨"Round", .exactly 1, floatToInt .fround⟩,
  ⟨"Int", .exactly 1, floatToInt .ftrunc⟩,
  ⟨"Floor", .exactly 1, elabFloorCeil false⟩,
  ⟨"Ceil", .exactly 1, elabFloorCeil true⟩,
  ⟨"Quotient", .exactly 2, failableInts .quotient⟩,
  ⟨"Mod", .exactly 2, failableInts .modulo⟩,
  ⟨"Min", .exactly 2, elabMinMax true⟩,
  ⟨"Max", .exactly 2, elabMinMax false⟩,
  ⟨"Clamp", .exactly 3, elabClampOrSgn⟩,
  ⟨"Sgn", .exactly 1, elabClampOrSgn⟩,
  ⟨"BitAnd", .exactly 2, elabBitwise false⟩,
  ⟨"BitOr", .exactly 2, elabBitwise false⟩,
  ⟨"BitXor", .exactly 2, elabBitwise false⟩,
  ⟨"BitNot", .exactly 1, elabBitwise false⟩,
  ⟨"BitShiftLeft", .exactly 2, elabBitwise true⟩,
  ⟨"BitShiftRight", .exactly 2, elabBitwise true⟩,
  ⟨"Err", .any, elabErr⟩,
  ⟨"$Show", .exactly 1, elabShow⟩]

/-- The built-in a call of `name` means, as a name of `builtinFunctions`
    (or none of them), and the name the call goes on with: `$F` is the
    built-in `F` whatever the program defines (as a prelude or a built-in's
    value definition calls it); a soft built-in (or `any`) the program
    defines is the program's, `$program`. -/
def builtinCalled (ctx : Ctx) (name : String) : String × String :=
  let hidden := (name.drop 1).toString
  let builtinName :=
    if name.startsWith "$" && (builtins.contains hidden || softBuiltins.contains hidden) then hidden
    else if (softBuiltins.contains name || name == "any") && (ctx.sig? name).isSome then "$program" else name
  (builtinName, if builtinName == "$program" then name else builtinName)

end OpenVerse.Front
