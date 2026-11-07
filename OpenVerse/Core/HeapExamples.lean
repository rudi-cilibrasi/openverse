/-
  OpenVerse — hand-elaborated heap programs (#20, #29).

  The front end does not produce heap operations yet (#20, step 5), so these
  programs are written in Verse Core directly. The `example`s check, at build
  time, that the type checker accepts the typed ones (so `Runs.typed`
  applies to them), that it rejects the ill-typed ones, and what the
  reference interpreter prints.
-/
import OpenVerse.Core.Examples
import OpenVerse.Core.Check
import OpenVerse.Core.Control
import OpenVerse.Core.TypeCheck

namespace OpenVerse.HeapExamples
open Expr OpenVerse.Examples

/-- Two classes: `point` (tag 0) with fields `X, Y : int`, and its subclass
    `point3` (tag 1) with `X, Y, Z : int`. A reference of type `.ref [0, 1]`
    is a `point` that may be a `point3`. -/
def classes : List (List VTy) := [[.int, .int], [.int, .int, .int]]

/-- ```verse
    Show(P:point):void =
        set P.X = 10
        Print("{P.X}")
        if (point3[P]) { Print("a point3") } else { Print("not a point3") }
        if (set P.Y = 99, point3[P], false?) {}  # fails: the write is undone
        Print("{P.Y}")
        Print("{ClassTag(P)}")
        if (P3 := point3[P]) { Print("{P3.Z}") }
    Main():void =
        P:point = point3{X := 1, Y := 2, Z := 3}
        Show(P)
    ```
    A slot starts with a default of its type. No literal is a reference, so
    `P3`'s slot (1) and `Main`'s `P` start as new objects with default fields
    (`DefaultE.new`), which the program then never reads. -/
def heapDemo : Prog where
  fns := [
    { name := "Show", arity := 1, nslots := 2, decides := false,
      body := .seq (.assign 1 (.heap (.new 1) [int 0, int 0, int 0]))
        (.seq (.heap (.set 0) [.local 0, int 10])
        (.seq (printInt (.heap (.get 0) [.local 0]))
        (.seq (.ite (.heap (.isTag [1]) [.local 0])
                (.print (str "a point3")) (.print (str "not a point3")))
        (.seq (.ite (.seq (.heap (.set 1) [.local 0, int 99])
                  (.seq (.heap (.isTag [1]) [.local 0]) (p .fail [])))
                (.lit .void) (.lit .void))
        (.seq (printInt (.heap (.get 1) [.local 0]))
        (.seq (printInt (.heap .tag [.local 0]))
        (.ite (.assign 1 (.heap (.isTag [1]) [.local 0]))
          (printInt (.heap (.get 2) [.local 1])) (.lit .void)))))))) },
    { name := "Main", arity := 0, nslots := 1, decides := false,
      body := .seq (.assign 0 (.heap (.new 0) [int 0, int 0]))
        (.seq (.assign 0 (.heap (.new 1) [int 1, int 2, int 3]))
          (.call 0 [.local 0])) }]
  main := 1

/-- The signatures and class table of `heapDemo`. -/
def heapSigs : Sigs := { fns := [([.ref [0, 1]], .void), ([], .void)], classes }
def heapSlots : List (List VTy) := [[.ref [0, 1], .ref [1]], [.ref [0, 1]]]

example : heapDemo.check = true := by native_decide
example : heapDemo.checkControl = true := by native_decide
example : heapDemo.checkTypes heapSigs heapSlots = true := by native_decide
example : outOf heapDemo = some (.ok .void, "10\na point3\n2\n1\n3\n") := by native_decide

/-- The heap programs, for `openverse example` (the C runtime runs them, #31). -/
def all : List (String × Prog) := [("heap", heapDemo)]

/-- A cast outside a failure context makes `Show` failable: `Prog.check`
    rejects it unless `Show` is `<decides>`. -/
def castOutside : Prog :=
  { heapDemo with fns := heapDemo.fns.set 0 { heapDemo.fns[0]! with
      body := .seq (.assign 1 (.heap (.new 1) [int 0, int 0, int 0]))
        (printInt (.heap (.get 2) [.heap (.isTag [1]) [.local 0]])) } }
example : castOutside.check = false := by native_decide
example : castOutside.checkTypes heapSigs heapSlots = true := by native_decide

/-! ### What the checker rejects -/

section
/-- `tc` in `Show`'s context: slot 0 is a `point` that may be a `point3`. -/
def tcShow (e : Expr) (m : Option VTy) : Option VTy :=
  tc heapSigs [.ref [0, 1], .ref [1]] .void e m

-- `point` has no field `Z`: reading it needs a cast to `point3`
example : tcShow (.heap (.get 2) [.local 0]) none = none := by native_decide
example : tcShow (.heap (.get 2) [.heap (.isTag [1]) [.local 0]]) none = some .int := by native_decide
-- a field keeps its type
example : tcShow (.heap (.set 0) [.local 0, str "ten"]) none = none := by native_decide
-- a `point` is not known to be a `point3` (no implicit downcast) ...
example : tcShow (.local 0) (some (.ref [1])) = none := by native_decide
-- ... but it is anything that includes `point` and `point3` (upcast)
example : tcShow (.local 0) (some (.ref [0, 1, 2])) = some (.ref [0, 1, 2]) := by native_decide
-- `new` checks the fields against the class
example : tcShow (.heap (.new 0) [int 1]) none = none := by native_decide
example : tcShow (.heap (.new 0) [int 1, str "y"]) none = none := by native_decide
example : tcShow (.heap (.new 0) [int 1, int 2]) none = some (.ref [0]) := by native_decide
example : tcShow (.heap (.new 0) [int 1, int 2]) (some (.ref [1])) = none := by native_decide
-- a slot keeps its type: `P3` cannot hold a `point`
example : tcShow (.assign 1 (.local 0)) none = none := by native_decide
-- a reference is not an int
example : tcShow (p .add [.local 0, int 1]) none = none := by native_decide
end

-- defaults: a new object of a class of the slot's type, with default fields,
-- or a parameter of fewer classes
example : checkDefault heapSigs 1 [.ref [0, 1], .ref [1]] (.heap (.new 1) [int 0, int 0, int 0]) (.ref [1]) = true := by
  native_decide
example : checkDefault heapSigs 1 [.ref [0, 1], .ref [1]] (.heap (.new 0) [int 0, int 0]) (.ref [1]) = false := by
  native_decide
example : checkDefault heapSigs 1 [.ref [0, 1], .ref [1]] (.heap (.new 1) [int 0, int 0]) (.ref [1]) = false := by
  native_decide
example : checkDefault heapSigs 1 [.ref [1], .ref [0, 1]] (.local 0) (.ref [0, 1]) = true := by native_decide
example : checkDefault heapSigs 1 [.ref [0, 1], .ref [1]] (.local 0) (.ref [1]) = false := by native_decide
-- a default reads only parameters
example : checkDefault heapSigs 1 [.ref [0, 1], .ref [0, 1]] (.local 1) (.ref [0, 1]) = false := by native_decide

/-! ### Subtyping (#32) -/

/-- ```verse
    Make3(X:int):point3 = point3{X := X, Y := X + 1, Z := X + 2}
    SumX(Ps:[]point):int =
        var T:int = 0
        for (P : Ps) { set T += P.X }
        T
    Show(P:point):void = Print("{P.X}")
    Main():void =
        Show(Make3(5))                    # a call result, widened
        Ps:[]point = array{Make3(1), Make3(2)}
        Print("{SumX(Ps)}")
        Qs:[]point3 = array{Make3(10)}
        Print("{SumX(Qs)}")               # []point3 is a []point
        O:?point = option{Make3(7)}
        if (Show(O?)) {}
        if (Show(point3[Ps[0]])) {}       # a cast, widened
    ``` -/
def subDemo : Prog where
  fns := [
    { name := "Make3", arity := 1, nslots := 1, decides := false,
      body := .heap (.new 1) [.local 0, p .add [.local 0, int 1], p .add [.local 0, int 2]] },
    { name := "SumX", arity := 1, nslots := 3, decides := false,
      body := .seq (.assign 1 (.heap (.new 0) [int 0, int 0]))
        (.seq (.assign 2 (int 0))
        (.seq (.forE 1 (.local 0) (.lit (.logic true))
                (.assign 2 (p .add [.local 2, .heap (.get 0) [.local 1]])))
          (.local 2))) },
    { name := "Show", arity := 1, nslots := 1, decides := false,
      body := printInt (.heap (.get 0) [.local 0]) },
    { name := "Main", arity := 0, nslots := 3, decides := false,
      body := .seq (.assign 0 (.lit (.arr []))) (.seq (.assign 1 (.lit (.arr []))) (.seq (.assign 2 (.lit .none))
        (.seq (.call 2 [.call 0 [int 5]])
        (.seq (.assign 0 (p .mkArr [.call 0 [int 1], .call 0 [int 2]]))
        (.seq (printInt (.call 1 [.local 0]))
        (.seq (.assign 1 (p .mkArr [.call 0 [int 10]]))
        (.seq (printInt (.call 1 [.local 1]))
        (.seq (.assign 2 (p .mkSome [.call 0 [int 7]]))
        (.seq (.ite (.call 2 [p .query [.local 2]]) (.lit .void) (.lit .void))
          (.ite (.call 2 [.heap (.isTag [1]) [p .index [.local 0, int 0]]]) (.lit .void) (.lit .void))))))))))) }]
  main := 3

def subSigs : Sigs :=
  { fns := [([.int], .ref [1]), ([.arr (.ref [0, 1])], .int), ([.ref [0, 1]], .void), ([], .void)], classes }
def subSlots : List (List VTy) :=
  [[.int], [.arr (.ref [0, 1]), .ref [0, 1], .int], [.ref [0, 1]],
   [.arr (.ref [0, 1]), .arr (.ref [1]), .opt (.ref [0, 1])]]

example : subDemo.check = true := by native_decide
example : subDemo.checkTypes subSigs subSlots = true := by native_decide
example : outOf subDemo = some (.ok .void, "5\n3\n10\n7\n1\n") := by native_decide

section
/-- `tc` in `Main`'s context. -/
def tcMain (e : Expr) (m : Option VTy) : Option VTy :=
  tc subSigs [.arr (.ref [0, 1]), .arr (.ref [1]), .opt (.ref [0, 1])] .void e m

-- a call result, a cast, an option and an array widen ...
example : tcMain (.call 0 [int 1]) (some (.ref [0, 1])) = some (.ref [0, 1]) := by native_decide
example : tcMain (.heap (.isTag [1]) [p .index [.local 0, int 0]]) (some (.ref [0, 1])) = some (.ref [0, 1]) := by
  native_decide
example : tcMain (.local 1) (some (.arr (.ref [0, 1]))) = some (.arr (.ref [0, 1])) := by native_decide
example : tcMain (p .mkSome [.call 0 [int 1]]) (some (.opt (.ref [0, 1]))) = some (.opt (.ref [0, 1])) := by
  native_decide
-- ... but nothing narrows: a []point is not a []point3, a point3 result is not a `ref [0]`
example : tcMain (.local 0) (some (.arr (.ref [1]))) = none := by native_decide
example : tcMain (.call 0 [int 1]) (some (.ref [0])) = none := by native_decide
-- an array updated with a `point` is no longer a []point3, so it cannot go back into `Qs`
example : tcMain (.assign 1 (p .arrSet [.local 1, int 0, .heap (.new 0) [int 0, int 0]])) none = none := by
  native_decide
example : tcMain (.assign 0 (p .arrSet [.local 0, int 0, .heap (.new 0) [int 0, int 0]])) none =
    some (.arr (.ref [0, 1])) := by native_decide
-- tuples widen pointwise, with the same length
example : (VTy.tup [.ref [1], .int]).sub (.tup [.ref [0, 1], .int]) = true := by native_decide
example : (VTy.tup [.ref [1]]).sub (.tup [.ref [0, 1], .int]) = false := by native_decide
end

-- a class table with a type variable is refused (so `Typed.subst` holds)
example : heapDemo.checkTypes { heapSigs with classes := [[.var 0], [.int, .int, .int]] } heapSlots = false := by
  native_decide

end OpenVerse.HeapExamples
