/-
  OpenVerse — the syntax of Verse Core.

  Verse Core is what the front end (`OpenVerse.Front`) elaborates surface Verse
  into. Names are resolved: a local is a slot index into the frame of the
  current call, a function is an index into the program.

  The surface constructs that are *not* primitive here are derived forms,
  defined in `OpenVerse.Core.Derived` and proved to behave as the Book of Verse
  says (`not`, `or`, `and`, `option{}`, `if` without `else`, multi-clause
  `for`).
-/
import OpenVerse.Core.Value

namespace OpenVerse

/-- Primitive operations. Each is a function of the values of its arguments
    (`Prim.apply`); only `print` (a separate node) touches the output. -/
inductive Prim where
  -- int arithmetic (overflow is a runtime error)
  | add | sub | mul | neg | abs
  -- failable integer division (fail when the divisor is 0):
  -- `Floor(X/Y)`, `Ceil(X/Y)`, and the Euclidean `Quotient[X,Y]`, `Mod[X,Y]`
  | floorDiv | ceilDiv | quotient | modulo
  -- comparisons (failable: fail when false; succeed with the left operand)
  | lt | le | gt | ge | eq | ne
  -- `X?` : fail on `false` / empty option, else the payload
  | query
  -- construction
  | mkArr | mkTup | mkSome
  -- arrays and strings
  | concat | index | len | arrSet
  -- `for` support: concatenate an array of arrays; the inclusive range `a..b`
  | flatten | range
  -- `t(k)`: the k-th element of a tuple
  | tupGet (k : Nat)
  -- `ToString(x)`
  | toStr
  -- `false?` : always fails
  | fail
  -- `Err()` : runtime error
  | userErr
  -- floats (#127): IEEE arithmetic, canonical results; `Min`/`Max` (NaN if
  -- either is); orderings (failable, as `lt`…: fail on NaN); `int` to
  -- `float`; and `Floor`, `Ceil`, `Round` (ties to even), `Int` to `int`
  -- (failable: NaN, an infinity; out of range, the overflow error)
  | fadd | fsub | fmul | fdiv | fneg | fabs | fmin | fmax
  | flt | fle | fgt | fge
  | fofInt | ffloor | fceil | fround | ftrunc
  -- a float literal in the binary format: the float of an int's bits
  | fofBits
  -- the mathematical functions (#132): `Sqrt`, `Exp`, `Ln`, `Sin`, `Cos`,
  -- `Tan`, `ArcSin`, `ArcCos` (clamping to [-1, 1]), `ArcTan`; `Pow`,
  -- `ArcTan(Y, X)`; `IsFinite[F]` (failable)
  | fsqrt | fexp | fln | fsin | fcos | ftan | fasin | facos | fatan
  | fpow | fatan2 | fisFinite
  deriving Repr, DecidableEq, Inhabited

/-- Operations on the heap (#20). Each is a function of the values of its
    arguments and of the heap (`HeapOp.apply`). -/
inductive HeapOp where
  /-- Allocate an object of class `tag` with the arguments as its fields;
      the result is a reference to it. -/
  | new (tag : Nat)
  /-- `[r]`: field `k` of the object `r` refers to. -/
  | get (k : Nat)
  /-- `[r, v]`: set field `k` of the object `r` refers to; the result is `v`. -/
  | set (k : Nat)
  /-- `[r]`: the class of the object `r` refers to, as an `int`. -/
  | tag
  /-- `[r]`: `r`, if its object's class is one of `us`; fails otherwise (a cast). -/
  | isTag (us : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Verse Core expressions. -/
inductive Expr where
  /-- A literal value. -/
  | lit    : Value → Expr
  /-- Read slot `i` of the current frame. -/
  | local  : Nat → Expr
  /-- Evaluate `e`, store its value in slot `i`; the result is that value.
      Elaborates both `X := e` / `X:t = e` (first binding) and `set X = e`. -/
  | assign : Nat → Expr → Expr
  /-- `a` then `b`; the value of `a` is discarded. -/
  | seq    : Expr → Expr → Expr
  /-- A primitive applied to arguments evaluated left to right. -/
  | prim   : Prim → List Expr → Expr
  /-- Call function number `f` with arguments evaluated left to right. -/
  | call   : Nat → List Expr → Expr
  /-- `if (c) then t else e`. `c` is a failure context: if it fails, its
      effects are rolled back and `e` runs from the state before `c`.
      Bindings made by `c` are visible in `t`. -/
  | ite    : Expr → Expr → Expr → Expr
  /-- `for (X : it, filt) { body }` for one generator. Each element is bound
      to slot `i`; `filt` is a failure context: when it fails, its effects
      are rolled back and the element is skipped. The result is the array of
      the values of `body`. -/
  | forE   : Nat → Expr → Expr → Expr → Expr
  /-- `loop: body`, left by `break` (value `void`) or `return`. -/
  | loop   : Expr → Expr
  /-- `break`. -/
  | brk    : Expr
  /-- `return e`. -/
  | ret    : Expr → Expr
  /-- `Print(e)`: append the bytes of the string `e` and a newline to the output. -/
  | print  : Expr → Expr
  /-- A heap operation applied to arguments evaluated left to right. -/
  | heap   : HeapOp → List Expr → Expr
  deriving Repr, Inhabited

/-- A function of the program. Its frame has `nslots` slots; the first
    `arity` hold the arguments, the others start as `void`. -/
structure Fn where
  name    : String
  arity   : Nat
  nslots  : Nat
  /-- `<decides>`: calls may fail (and must be written `F[…]`). -/
  decides : Bool
  body    : Expr
  /-- Calls may change an existing object (#35): `false` for a function
      whose effects exclude `writes` (`<computes>`, `<reads>`, `<allocates>`). -/
  writes  : Bool := true
  deriving Repr, Inhabited

/-- A program: its functions, and the index of `Main`. -/
structure Prog where
  fns  : List Fn
  main : Nat
  deriving Repr, Inhabited

end OpenVerse
