import OpenVerse.Core.Float
/-
  OpenVerse — values of Verse Core.

  Verse values are immutable. Strings are arrays of `char` (UTF-8 code units),
  exactly as in Verse, where `string` is an alias of `[]char`. Options are
  represented by the two constructors `none` (written `false` in Verse) and
  `some`.

  `int` is Verse's 64-bit signed integer. Values of `int` always lie in
  [`Int64.minV`, `Int64.maxV`]; an operation whose mathematical result lies
  outside is a runtime error (`ErrKind.overflow`), never a wrap-around.
-/
namespace OpenVerse

/-- Smallest Verse `int`. -/
def Int64.minV : Int := -9223372036854775808
/-- Largest Verse `int`. -/
def Int64.maxV : Int := 9223372036854775807

/-- `i` is representable as a Verse `int`. -/
def Int64.inRange (i : Int) : Bool := decide (Int64.minV ≤ i) && decide (i ≤ Int64.maxV)

inductive Value where
  /-- `int`; invariant (not enforced by the type): `Int64.inRange i`. -/
  | int   : Int → Value
  /-- `logic`: `true` / `false`. -/
  | logic : Bool → Value
  /-- `char`: one UTF-8 code unit, `0 ≤ c < 256`. -/
  | char  : Nat → Value
  /-- `float` (#127): the bits of an IEEE 64-bit float, canonical (one NaN,
      no negative zero: `Float.canon`), so that equality of values is Verse's
      equality of floats. -/
  | float : UInt64 → Value
  /-- `[]t`, including `string = []char`. An `Array`, so that the
      reference interpreter indexes in constant time (#110); proofs reason
      about its `toList`. -/
  | arr   : Array Value → Value
  /-- `tuple(t₁, …, tₙ)`; `tup []` is the value of `void`. -/
  | tup   : List Value → Value
  /-- The empty option, written `false` in Verse. -/
  | none  : Value
  /-- `option{v}`. -/
  | some  : Value → Value
  /-- A reference to object `a` of the heap (a class instance, #20). -/
  | ref   : Nat → Value
  deriving Repr, Inhabited

namespace Value

/-- The unit value returned by `void` expressions. -/
def void : Value := .tup []

/-- Construct an integer value. Compiled code shares the wrappers for 0..1025. -/
def ofInt (i : Int) : Value := .int i

@[simp] theorem ofInt_eq_int (i : Int) : ofInt i = .int i := rfl

private def smallInts : Array Value :=
  Array.ofFn fun i : Fin 1026 => .int (i.val : Int)

private def ofIntCached : Int → Value
  | .ofNat n =>
    if h : n < 1026 then smallInts[n]'(by simpa [smallInts] using h)
    else .int (.ofNat n)
  | .negSucc n => .int (.negSucc n)

/-- Pooling changes physical sharing only, including at the cache boundaries. -/
@[csimp] private theorem ofInt_eq_ofIntCached : @ofInt = @ofIntCached := by
  funext i
  cases i with
  | ofNat n =>
    by_cases h : n < 1026 <;> simp [ofInt, ofIntCached, smallInts, h]
  | negSucc n => rfl

/-- Build a Verse string from a Lean string (UTF-8 bytes). -/
def ofString (s : String) : Value := .arr (s.toUTF8.toList.map fun b => .char b.toNat).toArray

mutual
/-- Decidable equality, written by hand: Lean cannot derive it for a nested inductive. -/
def decEq : (a b : Value) → Decidable (a = b)
  | .int x, .int y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .logic x, .logic y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .char x, .char y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .float x, .float y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .arr a, .arr b =>
    -- (the sizes first, in constant time: arrays of different lengths are
    -- told apart without walking them)
    if hl : a.size = b.size then
      match decEqList a.toList b.toList with
      | isTrue h => isTrue (congrArg Value.arr (Array.toList_inj.mp h))
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    else isFalse (by intro h'; cases h'; exact hl rfl)
  | .tup xs, .tup ys => match decEqList xs ys with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .none, .none => isTrue rfl
  | .some x, .some y => match decEq x y with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ref x, .ref y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .int _, .ref _ | .logic _, .ref _ | .char _, .ref _ | .arr _, .ref _ | .tup _, .ref _ | .none, .ref _
  | .some _, .ref _ => isFalse (by intro h; cases h)
  | .ref _, .int _ | .ref _, .logic _ | .ref _, .char _ | .ref _, .arr _ | .ref _, .tup _ | .ref _, .none
  | .ref _, .some _ => isFalse (by intro h; cases h)
  | .int _, .logic _ | .int _, .char _ | .int _, .arr _ | .int _, .tup _ | .int _, .none | .int _, .some _ => isFalse (by intro h; cases h)
  | .logic _, .int _ | .logic _, .char _ | .logic _, .arr _ | .logic _, .tup _ | .logic _, .none | .logic _, .some _ => isFalse (by intro h; cases h)
  | .char _, .int _ | .char _, .logic _ | .char _, .arr _ | .char _, .tup _ | .char _, .none | .char _, .some _ => isFalse (by intro h; cases h)
  | .arr _, .int _ | .arr _, .logic _ | .arr _, .char _ | .arr _, .tup _ | .arr _, .none | .arr _, .some _ => isFalse (by intro h; cases h)
  | .tup _, .int _ | .tup _, .logic _ | .tup _, .char _ | .tup _, .arr _ | .tup _, .none | .tup _, .some _ => isFalse (by intro h; cases h)
  | .none, .int _ | .none, .logic _ | .none, .char _ | .none, .arr _ | .none, .tup _ | .none, .some _ => isFalse (by intro h; cases h)
  | .some _, .int _ | .some _, .logic _ | .some _, .char _ | .some _, .arr _ | .some _, .tup _ | .some _, .none => isFalse (by intro h; cases h)
  | .float _, .int _ | .float _, .logic _ | .float _, .char _ | .float _, .arr _ | .float _, .tup _
  | .float _, .none | .float _, .some _ | .float _, .ref _
  | .int _, .float _ | .logic _, .float _ | .char _, .float _ | .arr _, .float _ | .tup _, .float _
  | .none, .float _ | .some _, .float _ | .ref _, .float _ => isFalse (by intro h; cases h)
def decEqList : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs => match decEq a b, decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
end

instance : DecidableEq Value := decEq

/-- Render a value the way the reference implementation prints it (`ToString`). -/
partial def render : Value → String
  | .int i => toString i
  | .logic b => if b then "true" else "false"
  | .char c => String.singleton (Char.ofNat c)
  | .float b => VFloat.render b
  | .arr vs =>
    if vs.all (fun v => match v with | .char _ => true | _ => false) && !vs.isEmpty then
      String.fromUTF8! (ByteArray.mk (vs.map (fun v => match v with
        | .char c => c.toUInt8 | _ => 0)))
    else "array{" ++ ", ".intercalate (vs.toList.map render) ++ "}"
  | .tup vs => "(" ++ ", ".intercalate (vs.map render) ++ ")"
  | .none => "false"
  | .some v => "option{" ++ render v ++ "}"
  | .ref a => s!"ref {a}"

end Value

/-- Runtime errors. They end the whole program; failure contexts do not catch them. -/
inductive ErrKind where
  /-- An `int` result outside the 64-bit range. -/
  | overflow
  /-- An operation applied to values of the wrong shape (excluded by the type checker). -/
  | type
  /-- A slot index outside the current frame (excluded by the loader / elaborator). -/
  | slot
  /-- A call to a function that does not exist or with the wrong number of arguments. -/
  | call
  /-- `break` outside `loop`, or `return` reaching a place it cannot. -/
  | control
  /-- An explicit `Err()` call. -/
  | user
  deriving Repr, DecidableEq, Inhabited

/-- The outcome of evaluating one expression. -/
inductive Res where
  /-- Success with a value. -/
  | ok   : Value → Res
  /-- Verse failure: caught by the nearest failure context, which rolls back. -/
  | fail : Res
  /-- `break` travelling to the nearest `loop`. -/
  | brk  : Res
  /-- `return v` travelling to the function boundary. -/
  | ret  : Value → Res
  /-- A runtime error: ends the program. -/
  | err  : ErrKind → Res
  deriving Repr, DecidableEq, Inhabited

namespace Res
/-- Is this the normal (successful) outcome? -/
def isOk : Res → Bool
  | .ok _ => true
  | _ => false

@[simp] theorem isOk_ok (v : Value) : (Res.ok v).isOk = true := rfl
@[simp] theorem isOk_fail : Res.fail.isOk = false := rfl
@[simp] theorem isOk_brk : Res.brk.isOk = false := rfl
@[simp] theorem isOk_ret (v : Value) : (Res.ret v).isOk = false := rfl
@[simp] theorem isOk_err (e : ErrKind) : (Res.err e).isOk = false := rfl

/-- Range-checked `int` result. -/
def ofInt (i : Int) : Res := if Int64.inRange i then .ok (Value.ofInt i) else .err .overflow
end Res

/-- The outcome of evaluating a list of expressions left to right. -/
inductive LRes where
  | ok   : List Value → LRes
  /-- The first abrupt (non-`ok`) outcome; never `Res.ok`. -/
  | stop : Res → LRes
  deriving Repr, DecidableEq, Inhabited

end OpenVerse
