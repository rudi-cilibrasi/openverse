/-
  OpenVerse front end — a module constant is evaluated in 64 bits (#724).

  Ints go past 64 bits at run time, as on Epic's Verse VM, but Epic's compiler
  evaluates a module's constants when it links the module, with 64-bit
  ints: UEFN 43.12 with the Verse VM refuses
  `TwoTo64:int = (9223372036854775807 + 1) * 2` with error 9003, "Runtime
  error while evaluating module" (its log: "integer add overflow"), though
  the same arithmetic in a function gives 2^64 at run time
  (`tests/conformance/versevm/book/book-int-pow64-module-const.verse`;
  the Book's test, `Math/Bitwise.versetest:73`, expects it to run).

  openverse computes a constant at each use, at run time, and does not
  evaluate the program before it runs. So it refuses here, at compile time,
  the constants it can evaluate without running the program: those whose
  value is int arithmetic (`+`, `-`, `*`, negation, `Abs`, the divisions)
  on int literals and on other such constants, when a step of it leaves
  the 64-bit range. A constant whose value calls a function, reads a
  variable or builds anything else is computed at run time with the Verse
  VM's ints.
-/
import OpenVerse.Core.Prims

namespace OpenVerse.Front.ConstantRange

/-- What evaluating a constant's value in 64 bits gives: an int, a step
    outside the range (the Blueprint VM's name of the error and the step),
    or nothing known without running the program. -/
inductive Fold where
  | value (i : Int)
  | overflow (what : String)
  | unknown
  deriving Inhabited

/-- The name the Blueprint VM's runtime error gives a step that leaves the
    range (issue #724: "integer add overflow", …). -/
def errorName : Prim → String
  | .add => "integer add overflow"
  | .sub => "integer subtract overflow"
  | .mul => "integer multiply overflow"
  | .neg => "integer negate overflow"
  | .abs => "integer abs overflow"
  | _ => "integer divide overflow"

/-- The step, as Verse writes it. -/
def written (op : Prim) (args : List Int) : String :=
  match op, args.map toString with
  | .add, [x, y] => s!"{x} + {y}"
  | .sub, [x, y] => s!"{x} - {y}"
  | .mul, [x, y] => s!"{x} * {y}"
  | .neg, [x] => s!"-({x})"
  | .abs, [x] => s!"Abs({x})"
  | .floorDiv, [x, y] => s!"Floor({x} / {y})"
  | .ceilDiv, [x, y] => s!"Ceil({x} / {y})"
  | .quotient, [x, y] => s!"Quotient[{x}, {y}]"
  | .modulo, [x, y] => s!"Mod[{x}, {y}]"
  | _, a => ", ".intercalate a

/-- One step on known operands: its value, or the overflow. A division by
    zero fails, which a constant cannot: nothing known. -/
def step (op : Prim) (args : List Int) : Fold :=
  match op.apply (args.map Value.int) with
  | .ok (.int r) =>
    if Int64.inRange r then .value r
    else .overflow s!"{errorName op}: {written op args}"
  | _ => .unknown

/-- The int prims a constant's value may fold through. -/
def arith (op : Prim) : Bool :=
  [Prim.add, .sub, .mul, .floorDiv, .ceilDiv, .quotient, .modulo, .neg, .abs].contains op

/-- `e` evaluated in 64 bits, with `consts f` the value of constant `f` (a
    function of no parameters), through at most `depth` constants. Operands
    are evaluated left to right, so one that overflows before any unknown
    one is reached decides. -/
partial def fold (consts : Nat → Option Expr) : Nat → Expr → Fold
  | _, .lit (.int i) => .value i
  | d + 1, .call f [] => match consts f with
    | some b => fold consts d b
    | none => .unknown
  | d + 1, .prim op es =>
    if !arith op || es.length > 2 then .unknown else
    let rec go : List Expr → List Int → Fold
      | [], acc => step op acc.reverse
      | e :: es, acc => match fold consts d e with
        | .value i => go es (i :: acc)
        | r => r
    go es []
  | _, _ => .unknown

/-- The overflow, if a constant's value, evaluated as Epic's linker
    evaluates it, leaves the 64-bit range. -/
def check (consts : Nat → Option Expr) (body : Expr) : Option String :=
  match fold consts 64 body with
  | .overflow what => some what
  | _ => none

end OpenVerse.Front.ConstantRange
