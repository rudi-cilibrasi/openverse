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
  match ← below 20 with
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
  | _ => if (← chance 15) then genIllTyped env (d-1) else return .lit (.int (← smallInt))

/-- A failable condition. -/
partial def genCond (env : Env) (d : Nat) : G Expr := do
  if d == 0 then return p .lt [← genInt env 0, ← genInt env 0]
  match ← below 8 with
  | 0 | 1 | 2 => return p (← pick [.lt, .le, .gt, .ge, .eq, .ne]) [← genInt env (d-1), ← genInt env (d-1)]
  | 3 => return .seq (← genStmt env (d-1)) (← genCond env (d-1))
  | 4 => return .ite (← genCond env (d-1)) (p .fail []) (.lit .void)  -- `not`
  | 5 => return p .query [.lit (.logic (← chance 50))]
  | 6 => return p .index [← genArr env (d-1), ← genInt env (d-1)]
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
  | 2 => return p .concat [← genArr env (d-1), ← genArr env (d-1)]
  | 3 | 4 =>
    if env.slots > 0 then
      return .forE (← below env.slots) (← genArr env (d-1)) (← genCond env (d-1)) (← genInt env (d-1))
    else genArr env 0
  | _ => return p .flatten [p .mkArr [← genArr env (d-1), ← genArr env (d-1)]]

/-- A statement (its value is not interesting). -/
partial def genStmt (env : Env) (d : Nat) : G Expr := do
  if d == 0 then return .print (p .toStr [← genInt env 0])
  match ← below 11 with
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
  | _ => return .print (.lit (Value.ofString (← pick ["a", "", "rolled?", "x y"])))

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
      let tail ← genInt env 2
      -- start the non-parameter slots as ints (they begin as `void`)
      let init := (List.range extra).foldr (fun k e => Expr.seq (.assign (arity + k) (.lit (.int k))) e)
        (.lit .void)
      -- at most 12 nested loops per function: reserve that many counter slots
      fns := fns.push { name := s!"f{i}", arity, nslots := slots + 12, decides := ← chance 30,
                        body := .seq init (.seq body tail) }
    return { fns := fns.toList, main := nfns }
  return (go.run' s0)

end OpenVerse.Gen
