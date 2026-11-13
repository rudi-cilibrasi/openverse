/-
  OpenVerse — random Verse Core programs for differential testing.

  `Gen.program seed` builds a well-scoped program (so the C loader accepts
  it) that always terminates: function `i` calls only functions `< i`, and
  every `loop` counts in a slot of its own up to a small bound. Everything
  else is random, including failable operations outside failure contexts,
  `break`/`return` in odd places, overflowing arithmetic and ill-typed
  primitive applications, so that the C runtime is compared with the
  reference interpreter on every kind of outcome. `scripts/fuzz-diff.sh`
  runs the comparison.
-/
import OpenVerse.Core.Syntax

namespace OpenVerse.Gen

abbrev G := StateM UInt64

def next : G UInt64 := modifyGet fun (s : UInt64) =>
  let x : UInt64 := s ^^^ (s <<< (13 : UInt64))
  let x : UInt64 := x ^^^ (x >>> (7 : UInt64))
  let x : UInt64 := x ^^^ (x <<< (17 : UInt64))
  (x, x)

def below (n : Nat) : G Nat := do
  if n == 0 then return 0
  return (← next).toNat % n

def chance (pct : Nat) : G Bool := do return (← below 100) < pct

def pick [Inhabited α] (xs : List α) : G α := do return xs[← below xs.length]!

structure Env where
  /-- Slots the generated code may read and write. -/
  slots  : Nat
  /-- Callable functions: index, arity. -/
  fns    : List (Nat × Nat)
  /-- Slots reserved as loop counters (never written by other code), next free. -/
  nextCounter : Nat
  deriving Inhabited

def p (op : Prim) (es : List Expr) : Expr := .prim op es

def smallInt : G Int := do
  match ← below 10 with
  | 0 => pick [9223372036854775807, -9223372036854775808, 4611686018427387904, -1, 0]
  | _ => return (← below 25 : Nat) - 5

mutual
partial def genInt (env : Env) (d : Nat) : G Expr := do
  if d == 0 then
    if env.slots > 0 && (← chance 50) then return .local (← below env.slots)
    return .lit (.int (← smallInt))
  match ← below 23 with
  | 0 | 1 => return .lit (.int (← smallInt))
  | 2 | 3 => if env.slots > 0 then return .local (← below env.slots) else genInt env 0
  | 4 => return p (← pick [.add, .sub, .mul]) [← genInt env (d-1), ← genInt env (d-1)]
  | 5 => return p (← pick [.add, .mul]) [← genInt env (d-1), ← genInt env (d-1)]
  | 6 => return p (← pick [.neg, .abs]) [← genInt env (d-1)]
  | 7 => return p (← pick [.floorDiv, .ceilDiv, .quotient, .modulo]) [← genInt env (d-1), ← genInt env (d-1)]
  | 8 =>
    match env.fns with
    | [] => genInt env (d-1)
    | fs =>
      let (f, a) ← pick fs
      let mut args := #[]
      for _ in [0:a] do args := args.push (← genInt env (d-1))
      return .call f args.toList
  | 9 | 10 => return .ite (← genCond env (d-1)) (← genInt env (d-1)) (← genInt env (d-1))
  | 11 => return .seq (← genStmt env (d-1)) (← genInt env (d-1))
  | 12 =>
    if env.slots > 0 then return .assign (← below env.slots) (← genInt env (d-1)) else genInt env 0
  | 13 => return p .index [← genArr env (d-1), ← genInt env (d-1)]
  | 14 => return p .len [← genArr env (d-1)]
  | 15 => return p (.tupGet 1) [p .mkTup [← genInt env (d-1), ← genInt env (d-1)]]
  | 16 => return p .query [p .mkSome [← genInt env (d-1)]]
  | 17 => return p (← pick [.lt, .le, .gt, .ge, .eq, .ne]) [← genInt env (d-1), ← genInt env (d-1)]
  | 18 => return .ite (← genCond env (d-1)) (← genInt env (d-1)) (.ret (← genInt env (d-1)))
  | 19 | 20 | 21 =>
    -- the heap (#31): a field, a field write, or a class tag
    match ← below 7 with
    | 0 | 1 => return .heap (.get (← below 2)) [← genRef env (d-1)]
    | 2 | 3 => return .heap (.set (← below 2)) [← genRef env (d-1), ← genInt env (d-1)]
    -- a field holding an array (values of the value heap in objects)
    | 4 => return p .len [.heap (.get (← below 2)) [← genRef env (d-1)]]
    | 5 => return p .index [.heap (.get (← below 2)) [← genRef env (d-1)], ← genInt env (d-1)]
    | _ => return .heap .tag [← genRef env (d-1)]
  | _ => if (← chance 15) then genIllTyped env (d-1) else return .lit (.int (← smallInt))

/-- A reference (often): a new object of class 0–2 with 0–3 int fields, a
    slot (which may hold one), a cast, or a reference literal (which may
    dangle). -/
partial def genRef (env : Env) (d : Nat) : G Expr := do
  match ← below 8 with
  | 0 | 1 | 2 =>
    let many ← chance 85
    let k ← below 2
    let n := if many then 2 + k else k
    let mut es := #[]
    for _ in [0:n] do
      let d' := if d == 0 then 0 else d-1
      es := es.push (← if (← chance 25) then genArr env d' else genInt env d')
    return .heap (.new (← below 3)) es.toList
  | 3 | 4 | 5 => if env.slots > 0 then return .local (← below env.slots) else genRef env 0
  | 6 => if d == 0 then genRef env 0 else return .heap (.isTag (← genTags)) [← genRef env (d-1)]
  | _ => return .lit (.ref (← below 4))

/-- A set of class tags, for a cast. -/
partial def genTags : G (List Nat) := do
  match ← below 4 with
  | 0 => return []
  | 1 => return [← below 3]
  | 2 => return [← below 3, ← below 3]
  | _ => return [0, 1, 2]

/-- A failable condition. -/
partial def genCond (env : Env) (d : Nat) : G Expr := do
  if d == 0 then return p .lt [← genInt env 0, ← genInt env 0]
  match ← below 10 with
  | 0 | 1 | 2 => return p (← pick [.lt, .le, .gt, .ge, .eq, .ne]) [← genInt env (d-1), ← genInt env (d-1)]
  | 3 => return .seq (← genStmt env (d-1)) (← genCond env (d-1))
  | 4 => return .ite (← genCond env (d-1)) (p .fail []) (.lit .void)  -- `not`
  | 5 => return p .query [.lit (.logic (← chance 50))]
  | 6 => return p .index [← genArr env (d-1), ← genInt env (d-1)]
  | 7 =>
    -- a cast, or a field write then a cast: rolled back when it fails
    if (← chance 50) then return .heap (.isTag (← genTags)) [← genRef env (d-1)]
    return .seq (.heap (.set (← below 2)) [← genRef env (d-1), ← genInt env (d-1)])
      (.heap (.isTag (← genTags)) [← genRef env (d-1)])
  | 8 => return p .eq [← genRef env (d-1), ← genRef env (d-1)]
  | _ => return .seq (← genCond env (d-1)) (← genCond env (d-1))

/-- An int array. -/
partial def genArr (env : Env) (d : Nat) : G Expr := do
  if d == 0 then return p .range [.lit (.int (← below 3 : Nat)), .lit (.int (← below 6 : Nat))]
  match ← below 6 with
  | 0 => return p .range [.lit (.int ((← below 5 : Nat) - 2 : Int)), .lit (.int (← below 6 : Nat))]
  | 1 =>
    let n ← below 4
    let mut es := #[]
    for _ in [0:n] do es := es.push (← genInt env (d-1))
    return p .mkArr es.toList
  | 2 =>
    if (← chance 30) then return .heap (.get (← below 2)) [← genRef env (d-1)]
    return p .concat [← genArr env (d-1), ← genArr env (d-1)]
  | 3 | 4 =>
    if env.slots > 0 then
      return .forE (← below env.slots) (← genArr env (d-1)) (← genCond env (d-1)) (← genInt env (d-1))
    else genArr env 0
  | _ => return p .flatten [p .mkArr [← genArr env (d-1), ← genArr env (d-1)]]

/-- A statement (its value is not interesting). -/
partial def genStmt (env : Env) (d : Nat) : G Expr := do
  if d == 0 then return .print (p .toStr [← genInt env 0])
  match ← below 15 with
  | 0 | 1 | 2 => return .print (p .toStr [← genInt env (d-1)])
  | 3 => return .print (p .concat [.lit (Value.ofString "s:"), p .toStr [← genInt env (d-1)]])
  | 4 =>
    if env.slots > 0 then return .assign (← below env.slots) (← genInt env (d-1)) else genStmt env 0
  | 5 => return .ite (← genCond env (d-1)) (← genStmt env (d-1)) (← genStmt env (d-1))
  | 6 =>
    if env.slots > 0 then
      return .forE (← below env.slots) (← genArr env (d-1)) (← genCond env (d-1)) (← genStmt env (d-1))
    else genStmt env 0
  | 7 =>
    -- a bounded loop: counter c counts to k, then break
    let c := env.nextCounter
    let k ← below 4
    let env' := { env with nextCounter := c + 1 }
    let body ← genStmt env' (d-1)
    let brkE ← if (← chance 20) then pure Expr.brk else pure (Expr.lit .void)
    return .seq (.assign c (.lit (.int 0)))
      (.loop (.seq (.ite (p .ge [.local c, .lit (.int k)]) .brk (.lit .void))
        (.seq (.assign c (p .add [.local c, .lit (.int 1)])) (.seq body brkE))))
  | 8 => return .seq (← genStmt env (d-1)) (← genStmt env (d-1))
  | 9 => if (← chance 30) then return .brk else return .ret (← genInt env (d-1))
  | 10 =>
    -- keep a reference in a slot, so later code reads and writes its object
    if env.slots > 0 then return .assign (← below env.slots) (← genRef env (d-1)) else genStmt env 0
  | 11 =>
    -- store a fresh array in a field (maybe of an object the caller passed)
    return .heap (.set (← below 2)) [← genRef env (d-1), ← genArr env (d-1)]
  | 12 | 13 => genValTest env (d-1)
  | _ => return .print (.lit (Value.ofString (← pick ["a", "", "rolled?", "x y"])))

/-- A value, often holding the empty value at some depth, in each of the
    four ways Verse Core holds it (`.logic false`, `()`, `none`, `[]`, also
    `""` and an empty `mkArr`/`mkTup`), so that `eq`, `ne`, a map's lookup
    (an array of key-value pairs searched by `eq` on the keys) and a search of
    an array by `eq` compare them across their representations. -/
partial def genVal (env : Env) (d : Nat) : G Expr := do
  let empty : G Expr := do
    match ← below 7 with
    | 0 => return .lit (.logic false)
    | 1 => return .lit .void
    | 2 => return .lit .none
    | 3 => return .lit Value.emptyArray
    | 4 => return .lit (Value.ofString "")
    | 5 => return p .mkArr []
    | _ => return p .mkTup []
  if d == 0 then
    if (← chance 60) then return ← empty
    return .lit (← pick [.int 0, .int 1, .logic true, .char 97, Value.ofString "a"])
  match ← below 9 with
  | 0 | 1 | 2 => empty
  | 3 => return p .mkSome [← genVal env (d-1)]
  | 4 | 5 =>
    let n ← below 3
    let mut es := #[]
    for _ in [0:n] do es := es.push (← genVal env (d-1))
    return p .mkArr es.toList
  | 6 | 7 =>
    let n ← below 3
    let mut es := #[]
    for _ in [0:n] do es := es.push (← genVal env (d-1))
    return p .mkTup es.toList
  | _ => genVal env 0

/-- A test of values with the empty value at some depth: `eq` or `ne` of two,
    a map's lookup by a key, or a search of an array, printed. -/
partial def genValTest (env : Env) (d : Nat) : G Expr := do
  let yn (c : Expr) : Expr := .ite c (.print (.lit (Value.ofString "y"))) (.print (.lit (Value.ofString "n")))
  match ← below 3 with
  | 0 => return yn (p (← pick [.eq, .ne]) [← genVal env d, ← genVal env d])
  | 1 =>
    -- a map: pairs of a key and an int, looked up as the front end does
    if env.slots == 0 then return yn (p .eq [← genVal env d, ← genVal env d])
    let t ← below env.slots
    let n ← below 4
    let mut ps := #[]
    for i in [0:n] do ps := ps.push (p .mkTup [← genVal env d, .lit (.int i)])
    let look := p .index [.forE t (p .mkArr ps.toList) (p .eq [p (.tupGet 0) [.local t], ← genVal env d])
      (p (.tupGet 1) [.local t]), .lit (.int 0)]
    return .ite look (.print (p .toStr [look])) (.print (.lit (Value.ofString "missing")))
  | _ =>
    -- a search: how many elements of an array are the value
    if env.slots == 0 then return yn (p .ne [← genVal env d, ← genVal env d])
    let t ← below env.slots
    let n ← below 4
    let mut es := #[]
    for _ in [0:n] do es := es.push (← genVal env d)
    return .print (p .toStr [p .len [.forE t (p .mkArr es.toList) (p .eq [.local t, ← genVal env d]) (.local t)]])

/-- A primitive applied to values of the wrong shape (a type error), or a
    stray `Err()`. -/
partial def genIllTyped (env : Env) (d : Nat) : G Expr := do
  match ← below 6 with
  | 0 => return p .add [← genArr env d, ← genInt env d]
  | 1 => return p .len [← genInt env d]
  | 2 => return p .toStr [← genArr env d]
  | 3 => return .print (← genInt env d)
  | 4 => return p .userErr []
  | _ => return p .query [← genInt env d]
end

/-- A random terminating, well-scoped program. -/
def program (seed : Nat) : Prog := Id.run do
  let s0 : UInt64 := (seed.toUInt64 * 6364136223846793005 + 1442695040888963407) ||| 1
  let go : G Prog := do
    let nfns ← below 4
    let mut fns : Array Fn := #[]
    for i in [0:nfns + 1] do
      let isMain := i == nfns
      let arity ← if isMain then pure 0 else below 3
      let extra ← below 3
      let slots := arity + extra
      -- loop counters live above the ordinary slots
      let env : Env := { slots, fns := (fns.toList.zip (List.range fns.size)).map fun (f, j) => (j, f.arity),
                         nextCounter := slots }
      let body ← genStmt env 4
      -- (Main first compares values with the empty value at some depth, so
      -- that most programs do before an error may end them)
      let body ← if isMain then do
          let mut tests := body
          for _ in [0:4] do tests := .seq (← genValTest env 3) tests
          pure tests
        else pure body
      let tail ← genInt env 2
      -- start the non-parameter slots as ints or objects (they begin as `void`)
      let mut init := Expr.lit .void
      for k in (List.range extra).reverse do
        let v ← if (← chance 35) then pure (Expr.heap (.new (← below 3)) [.lit (.int k), .lit (.int (k + 1))])
          else pure (.lit (.int k))
        init := .seq (.assign (arity + k) v) init
      -- at most 12 nested loops per function: reserve that many counter slots
      fns := fns.push { name := s!"f{i}", arity, nslots := slots + 12, decides := ← chance 30,
                        body := .seq init (.seq body tail) }
    return { fns := fns.toList, main := nfns }
  return (go.run' s0)

end OpenVerse.Gen
