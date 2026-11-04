/-
  OpenVerse — hand-elaborated Verse Core programs.

  Each example gives the Verse source it stands for. They exercise the
  runtime before the front end exists, and the `example` theorems check the
  reference interpreter on them at build time (by `decide`/`rfl` on `run`).
-/
import OpenVerse.Core.Interp

namespace OpenVerse.Examples
open Expr

def int (i : Int) : Expr := .lit (.int i)
def str (s : String) : Expr := .lit (Value.ofString s)
def p (op : Prim) (es : List Expr) : Expr := .prim op es
def printInt (e : Expr) : Expr := .print (p .toStr [e])

/-- ```verse
    Fib(N:int):int = if (N <= 1) then N else Fib(N - 1) + Fib(N - 2)
    Main():void = Print("{Fib(20)}")
    ``` -/
def fib : Prog where
  fns := [
    { name := "Fib", arity := 1, nslots := 1, decides := false,
      body := .ite (p .le [.local 0, int 1]) (.local 0)
        (p .add [.call 0 [p .sub [.local 0, int 1]], .call 0 [p .sub [.local 0, int 2]]]) },
    { name := "Main", arity := 0, nslots := 0, decides := false,
      body := printInt (.call 0 [int 20]) }]
  main := 1

/-- ```verse
    Main():void =
        var X:int = 0
        if (set X = 5, X > 10) { Print("big") } else { Print("rolled back") }
        Print("{X}")
        set X = 7
        Print("{X}")
    ``` -/
def rollback : Prog where
  fns := [
    { name := "Main", arity := 0, nslots := 1, decides := false,
      body := .seq (.assign 0 (int 0))
        (.seq (.ite (.seq (.assign 0 (int 5)) (p .gt [.local 0, int 10]))
                (.print (str "big")) (.print (str "rolled back")))
        (.seq (printInt (.local 0))
        (.seq (.assign 0 (int 7)) (printInt (.local 0))))) }]
  main := 0

/-- ```verse
    Main():void =
        Squares := for (X : array{1, 2, 3, 4, 5}, X > 2) { X * X }
        for (S : Squares) { Print("{S}") }
        Print("{Squares.Length}")
    ``` -/
def forFilter : Prog where
  fns := [
    { name := "Main", arity := 0, nslots := 3, decides := false,
      body := .seq (.assign 0 (.forE 1 (p .mkArr [int 1, int 2, int 3, int 4, int 5])
                      (p .gt [.local 1, int 2]) (p .mul [.local 1, .local 1])))
        (.seq (.forE 2 (.local 0) (.lit (.logic true)) (printInt (.local 2)))
          (printInt (p .len [.local 0]))) }]
  main := 0

/-- ```verse
    Main():void =
        var I:int = 1
        loop:
            set I = I * 3
            if (I > 1000000000000000000) { Print("{I}") }
    ``` -/
def overflow : Prog where
  fns := [
    { name := "Main", arity := 0, nslots := 1, decides := false,
      body := .seq (.assign 0 (int 1))
        (.loop (.seq (.assign 0 (p .mul [.local 0, int 3]))
          (.ite (p .gt [.local 0, int 1000000000000000000]) (printInt (.local 0)) (.lit .void)))) }]
  main := 0

/-- ```verse
    Half(N:int)<decides>:int = Mod[N, 2] = 0; Quotient[N, 2]
    Main():void =
        for (I := -3..4):
            if (H := Half[I]) then Print("{I} -> {H}") else Print("{I} is odd")
        if (not Half[7]) { Print("7 is odd") }
        Print("{Mod[-7, 2]} {Quotient[-7, 2]}")
    ``` -/
def decides : Prog where
  fns := [
    { name := "Half", arity := 1, nslots := 1, decides := true,
      body := .seq (p .eq [p .modulo [.local 0, int 2], int 0]) (p .quotient [.local 0, int 2]) },
    { name := "Main", arity := 0, nslots := 2, decides := false,
      body := .seq
        (.forE 0 (p .range [int (-3), int 4]) (.lit (.logic true))
          (.ite (.assign 1 (.call 0 [.local 0]))
            (.print (p .concat [p .toStr [.local 0], p .concat [str " -> ", p .toStr [.local 1]]]))
            (.print (p .concat [p .toStr [.local 0], str " is odd"]))))
        (.seq (.ite (.ite (.call 0 [int 7]) (p .fail []) (.lit .void)) (.print (str "7 is odd")) (.lit .void))
          (.print (p .concat [p .toStr [p .modulo [int (-7), int 2]],
                   p .concat [str " ", p .toStr [p .quotient [int (-7), int 2]]]]))) }]
  main := 1

def all : List (String × Prog) :=
  [("fib", fib), ("rollback", rollback), ("for", forFilter), ("overflow", overflow),
   ("decides", decides)]

/-- The output of a run, as a string (for the build-time checks below). -/
def outOf (P : Prog) (fuel : Nat := 100000) : Option (Res × String) :=
  (P.run fuel).map fun (r, out) => (r, String.fromUTF8! (ByteArray.mk (out.map (·.toUInt8)).toArray))

example : outOf rollback = some (.ok .void, "rolled back\n0\n7\n") := by native_decide
example : outOf forFilter = some (.ok .void, "9\n16\n25\n3\n") := by native_decide
example : outOf overflow = some (.err .overflow, "1350851717672992089\n4052555153018976267\n") := by native_decide
example : outOf decides = some (.ok .void,
  "-3 is odd\n-2 -> -1\n-1 is odd\n0 -> 0\n1 is odd\n2 -> 1\n3 is odd\n4 -> 2\n7 is odd\n1 -4\n") := by
  native_decide

end OpenVerse.Examples
