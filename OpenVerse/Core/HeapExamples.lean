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
    `point3` (tag 1) with `X, Y, Z : int`. A reference of type `.ref [0, 1] []`
    (no type arguments) is a `point` that may be a `point3`. -/
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
def heapSigs : Sigs := { fns := [([.ref [0, 1] []], .void), ([], .void)], classes }
def heapSlots : List (List VTy) := [[.ref [0, 1] [], .ref [1] []], [.ref [0, 1] []]]

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
  tc heapSigs [.ref [0, 1] [], .ref [1] []] .void e m

-- `point` has no field `Z`: reading it needs a cast to `point3`
example : tcShow (.heap (.get 2) [.local 0]) none = none := by native_decide
example : tcShow (.heap (.get 2) [.heap (.isTag [1]) [.local 0]]) none = some .int := by native_decide
-- a field keeps its type
example : tcShow (.heap (.set 0) [.local 0, str "ten"]) none = none := by native_decide
-- a `point` is not known to be a `point3` (no implicit downcast) ...
example : tcShow (.local 0) (some (.ref [1] [])) = none := by native_decide
-- ... but it is anything that includes `point` and `point3` (upcast)
example : tcShow (.local 0) (some (.ref [0, 1, 2] [])) = some (.ref [0, 1, 2] []) := by native_decide
-- `new` checks the fields against the class
example : tcShow (.heap (.new 0) [int 1]) none = none := by native_decide
example : tcShow (.heap (.new 0) [int 1, str "y"]) none = none := by native_decide
example : tcShow (.heap (.new 0) [int 1, int 2]) none = some (.ref [0] []) := by native_decide
example : tcShow (.heap (.new 0) [int 1, int 2]) (some (.ref [1] [])) = none := by native_decide
-- a slot keeps its type: `P3` cannot hold a `point`
example : tcShow (.assign 1 (.local 0)) none = none := by native_decide
-- a reference is not an int
example : tcShow (p .add [.local 0, int 1]) none = none := by native_decide
end

-- defaults: a new object of a class of the slot's type, with default fields,
-- or a parameter of fewer classes
example : checkDefault heapSigs 1 [.ref [0, 1] [], .ref [1] []] (.heap (.new 1) [int 0, int 0, int 0]) (.ref [1] []) = true := by
  native_decide
example : checkDefault heapSigs 1 [.ref [0, 1] [], .ref [1] []] (.heap (.new 0) [int 0, int 0]) (.ref [1] []) = false := by
  native_decide
example : checkDefault heapSigs 1 [.ref [0, 1] [], .ref [1] []] (.heap (.new 1) [int 0, int 0]) (.ref [1] []) = false := by
  native_decide
example : checkDefault heapSigs 1 [.ref [1] [], .ref [0, 1] []] (.local 0) (.ref [0, 1] []) = true := by native_decide
example : checkDefault heapSigs 1 [.ref [0, 1] [], .ref [1] []] (.local 0) (.ref [1] []) = false := by native_decide
-- a default reads only parameters
example : checkDefault heapSigs 1 [.ref [0, 1] [], .ref [0, 1] []] (.local 1) (.ref [0, 1] []) = false := by native_decide

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
  { fns := [([.int], .ref [1] []), ([.arr (.ref [0, 1] [])], .int), ([.ref [0, 1] []], .void), ([], .void)], classes }
def subSlots : List (List VTy) :=
  [[.int], [.arr (.ref [0, 1] []), .ref [0, 1] [], .int], [.ref [0, 1] []],
   [.arr (.ref [0, 1] []), .arr (.ref [1] []), .opt (.ref [0, 1] [])]]

example : subDemo.check = true := by native_decide
example : subDemo.checkTypes subSigs subSlots = true := by native_decide
example : outOf subDemo = some (.ok .void, "5\n3\n10\n7\n1\n") := by native_decide

section
/-- `tc` in `Main`'s context. -/
def tcMain (e : Expr) (m : Option VTy) : Option VTy :=
  tc subSigs [.arr (.ref [0, 1] []), .arr (.ref [1] []), .opt (.ref [0, 1] [])] .void e m

-- a call result, a cast, an option and an array widen ...
example : tcMain (.call 0 [int 1]) (some (.ref [0, 1] [])) = some (.ref [0, 1] []) := by native_decide
example : tcMain (.heap (.isTag [1]) [p .index [.local 0, int 0]]) (some (.ref [0, 1] [])) = some (.ref [0, 1] []) := by
  native_decide
example : tcMain (.local 1) (some (.arr (.ref [0, 1] []))) = some (.arr (.ref [0, 1] [])) := by native_decide
example : tcMain (p .mkSome [.call 0 [int 1]]) (some (.opt (.ref [0, 1] []))) = some (.opt (.ref [0, 1] [])) := by
  native_decide
-- ... but nothing narrows: a []point is not a []point3, a point3 result is not a `ref [0]`
example : tcMain (.local 0) (some (.arr (.ref [1] []))) = none := by native_decide
example : tcMain (.call 0 [int 1]) (some (.ref [0] [])) = none := by native_decide
-- an array updated with a `point` is no longer a []point3, so it cannot go back into `Qs`,
-- but it is a []point
example : tcMain (.assign 1 (p .arrSet [.local 1, int 0, .heap (.new 0) [int 0, int 0]])) none = none := by
  native_decide
example : tcMain (.assign 0 (p .arrSet [.local 1, int 0, .heap (.new 0) [int 0, int 0]])) none =
    some (.arr (.ref [0, 1] [])) := by native_decide
-- branches of different classes join, in either order, also where only inference is possible
-- (the receiver of a field read or write)
example : tcMain (.ite (.lit (.logic true)) (.call 0 [int 1]) (.heap (.new 0) [int 0, int 0])) none =
    some (.ref [1, 0] []) := by native_decide
example : tcMain (.ite (.lit (.logic true)) (.heap (.new 0) [int 0, int 0]) (.call 0 [int 1])) none =
    some (.ref [0, 1] []) := by native_decide
example : tcMain (.heap (.get 0) [.ite (.lit (.logic true)) (.call 0 [int 1]) (.heap (.new 0) [int 0, int 0])])
    none = some .int := by native_decide
example : tcMain (.heap (.set 1) [.ite (.lit (.logic true)) (.call 0 [int 1]) (.heap (.new 0) [int 0, int 0]),
    int 5]) none = some .int := by native_decide
-- ... but `Z` is not a field of the join
example : tcMain (.heap (.get 2) [.ite (.lit (.logic true)) (.call 0 [int 1]) (.heap (.new 0) [int 0, int 0])])
    none = none := by native_decide
example : tcMain (p .concat [.local 1, .local 0]) none = some (.arr (.ref [1, 0] [])) := by native_decide
-- a `for` over a []point3 with a `point` slot
example : tc subSigs [.arr (.ref [1] []), .ref [0, 1] [], .int] .int
    (.forE 1 (.local 0) (.lit (.logic true)) (.heap (.get 0) [.local 1])) none = some (.arr .int) := by
  native_decide
-- a default of a container type from a parameter of a narrower one
example : checkDefault subSigs 1 [.arr (.ref [1] []), .arr (.ref [0, 1] [])] (.local 0) (.arr (.ref [0, 1] [])) = true := by
  native_decide
-- a generic call: its type argument comes from the last argument (the front end's hidden
-- argument), and the others may be narrower; without it, the first argument found decides
def idSigs : Sigs := { fns := [([.var 0, .var 0], .var 0)], classes }
example : tc idSigs [.ref [1] [], .ref [0, 1] []] .void (.call 0 [.local 0, .local 1]) none = some (.ref [0, 1] []) := by
  native_decide
example : tc idSigs [.ref [1] [], .ref [0, 1] []] .void (.call 0 [.local 1, .local 0]) none = none := by
  native_decide
-- tuples widen pointwise, with the same length
example : (VTy.tup [.ref [1] [], .int]).sub (.tup [.ref [0, 1] [], .int]) = true := by native_decide
example : (VTy.tup [.ref [1] []]).sub (.tup [.ref [0, 1] [], .int]) = false := by native_decide
end

/-! ### Functions that do not write (#35) -/

/-- `Show` only reads its object, so it may be marked as not writing;
    `castOutside`'s `Show` may too. `heapDemo`'s `Show` writes `P.X`. -/
def readsOnly : Prog :=
  { subDemo with fns := subDemo.fns.set 2 { subDemo.fns[2]! with writes := false } }
example : readsOnly.check = true := by native_decide
def writesMarkedReads : Prog :=
  { heapDemo with fns := heapDemo.fns.set 0 { heapDemo.fns[0]! with writes := false } }
example : writesMarkedReads.check = false := by native_decide
-- a call of a writing function writes, also in a failure context
example : (Expr.ite (.call 0 [.local 0]) (.lit .void) (.lit .void)).writesHeap heapDemo = true := by
  native_decide
-- `castOutside`'s `Show` only reads, so it may be marked as not writing
example : ({ castOutside with fns := castOutside.fns.set 0 { castOutside.fns[0]! with writes := false } }
    : Prog).checkWriteSound = true := by native_decide
-- a function that only calls functions that do not write does not write either: `SumX` marked,
-- and `Main` (which calls only `Make3`, `SumX` and `Show`) marked too once `Make3` is
def readsOnly2 : Prog :=
  let mark (fs : List Fn) (i : Nat) : List Fn := fs.set i { fs[i]! with writes := false }
  { readsOnly with fns := mark (mark (mark readsOnly.fns 1) 0) 3 }
example : readsOnly2.check = true := by native_decide
-- ... but a function that calls a writing one, unmarked, cannot be marked
def callsWriter : Prog :=
  { heapDemo with fns := heapDemo.fns.set 1 { heapDemo.fns[1]! with writes := false } }
example : callsWriter.check = false := by native_decide

/-! ### Prototypes (#37) -/

/-- `$Main` allocates a `point3` prototype (address 0), then calls `Main`,
    whose `point3` slot starts as a reference to it: no allocation.
    `Show` prints a `point3`'s `Z`. -/
def protoDemo : Prog where
  fns := [
    { name := "Show", arity := 1, nslots := 1, decides := false,
      body := printInt (.heap (.get 2) [.local 0]) },
    { name := "Main", arity := 0, nslots := 1, decides := false,
      body := .seq (.assign 0 (.lit (.ref 0)))
        (.seq (.assign 0 (.heap (.new 1) [int 7, int 8, int 9]))
        (.seq (.call 0 [.local 0]) (.call 0 [.lit (.ref 0)]))) },
    { name := "$Main", arity := 0, nslots := 0, decides := false,
      body := protoPrelude [(1, [.int 0, .int 0, .int 0])] (.call 1 []) }]
  main := 2

def protoSigs : Sigs := { fns := [([.ref [1] []], .void), ([], .void), ([], .void)], classes, protos := [(1, [])] }
def protoSlots : List (List VTy) := [[.ref [1] []], [.ref [1] []], []]

example : protoDemo.check = true := by native_decide
example : protoDemo.checkTypes protoSigs protoSlots = true := by native_decide
example : outOf protoDemo = some (.ok .void, "9\n0\n") := by native_decide
-- the prelude must allocate exactly the prototypes, well typed
example : protoDemo.checkTypes { protoSigs with protos := [(0, [])] } protoSlots = false := by native_decide
example : ({ protoDemo with fns := protoDemo.fns.set 2 { protoDemo.fns[2]! with
    body := protoPrelude [(1, [.int 0, .int 0])] (.call 1 []) } } : Prog).checkTypes protoSigs protoSlots = false := by
  native_decide
-- without prototypes, a reference literal has no type
example : protoDemo.checkTypes { protoSigs with protos := [] } protoSlots = false := by native_decide
-- a prototype's type is inferred where nothing is expected (a field read's receiver)
example : tc protoSigs [.ref [1] []] .void (.heap (.get 2) [.lit (.ref 0)]) none = some .int := by native_decide
-- prototypes may refer to each other in a cycle: a `point3` prototype whose class table says
-- its fields are a `point` and a `point3` reference (no instance needs to be built first)
example :
    let S : Sigs := { fns := [([], .void), ([], .void)], classes := [[.ref [1] []], [.ref [0] []]], protos := [(0, []), (1, [])] }
    let P : Prog := { fns := [
      { name := "Main", arity := 0, nslots := 0, decides := false, body := .lit .void },
      { name := "$Main", arity := 0, nslots := 0, decides := false,
        body := protoPrelude [(0, [.ref 1]), (1, [.ref 0])] (.call 0 []) }], main := 1 }
    P.checkTypes S [[], []] = true := by native_decide

/-! ### Parametric classes (#39) -/

/-- `box(t)` (tag 0) has one field, `Value : t`: its field types mention
    its type parameter. A reference type carries the type arguments.
    ```verse
    box(t:type) := class:
        var Value:t
    Get(t:type, B:box(t)):t = B.Value
    Main():void =
        I := box(int){Value := 5}
        S := box(string){Value := "five"}
        set I.Value = Get(I) + 1
        Print("{Get(I)}")
        Print(Get(S))
    ```
    (`Get`'s type parameter is inferred from its argument here.) -/
def boxDemo : Prog where
  fns := [
    { name := "Get", arity := 1, nslots := 1, decides := false, body := .heap (.get 0) [.local 0] },
    { name := "Main", arity := 0, nslots := 2, decides := false,
      body := .seq (.assign 0 (.heap (.new 0) [int 0]))
        (.seq (.assign 1 (.heap (.new 0) [.lit (.arr [])]))
        (.seq (.assign 0 (.heap (.new 0) [int 5]))
        (.seq (.assign 1 (.heap (.new 0) [str "five"]))
        (.seq (.heap (.set 0) [.local 0, p .add [.call 0 [.local 0], int 1]])
        (.seq (printInt (.call 0 [.local 0]))
          (.print (.call 0 [.local 1]))))))) }]
  main := 1

def boxSigs : Sigs := { fns := [([.ref [0] [.var 0]], .var 0), ([], .void)], classes := [[.var 0]] }
def boxSlots : List (List VTy) := [[.ref [0] [.var 0]], [.ref [0] [.int], .ref [0] [VTy.str]]]

example : boxDemo.check = true := by native_decide
example : boxDemo.checkTypes boxSigs boxSlots = true := by native_decide
example : outOf boxDemo = some (.ok .void, "6\nfive\n") := by native_decide

section
def tcBox (e : Expr) (m : Option VTy) : Option VTy :=
  tc boxSigs [.ref [0] [.int], .ref [0] [VTy.str]] .void e m

-- a field has the type of the instance
example : tcBox (.heap (.get 0) [.local 0]) none = some .int := by native_decide
example : tcBox (.heap (.get 0) [.local 1]) none = some VTy.str := by native_decide
example : tcBox (.heap (.set 0) [.local 0, str "six"]) none = none := by native_decide
-- type arguments are invariant: a box(int) is not a box(string), nor a box of anything else
example : tcBox (.local 0) (some (.ref [0] [VTy.str])) = none := by native_decide
example : tcBox (.assign 1 (.local 0)) none = none := by native_decide
-- `new` takes its type arguments from the expected type, else from the fields
example : tcBox (.heap (.new 0) [int 1]) none = some (.ref [0] [.int]) := by native_decide
example : tcBox (.heap (.new 0) [int 1]) (some (.ref [0] [VTy.str])) = none := by native_decide
example : tcBox (.heap (.new 0) [.lit (.arr [])]) (some (.ref [0] [VTy.str])) = some (.ref [0] [VTy.str]) := by
  native_decide
-- branches join only at the same type arguments
example : tcBox (.ite (.lit (.logic true)) (.local 0) (.local 1)) none = none := by native_decide
-- a generic call instantiates its type parameter from the reference's arguments
example : tcBox (.call 0 [.local 1]) none = some VTy.str := by native_decide
end

-- a prototype carries its type arguments, which must be closed (so `Typed.subst` holds)
section
def boxProto : Prog :=
  { fns := [
      { name := "Main", arity := 0, nslots := 1, decides := false,
        body := .seq (.assign 0 (.lit (.ref 0))) (printInt (.heap (.get 0) [.local 0])) },
      { name := "$Main", arity := 0, nslots := 0, decides := false,
        body := protoPrelude [(0, [.int 4])] (.call 0 []) }], main := 1 }
def boxProtoSigs (args : List VTy) : Sigs :=
  { fns := [([], .void), ([], .void)], classes := [[.var 0]], protos := [(0, args)] }
example : boxProto.checkTypes (boxProtoSigs [.int]) [[.ref [0] [.int]], []] = true := by native_decide
example : outOf boxProto = some (.ok .void, "4\n") := by native_decide
example : boxProto.checkTypes (boxProtoSigs [.var 0]) [[.ref [0] [.var 0]], []] = false := by native_decide
end

end OpenVerse.HeapExamples
