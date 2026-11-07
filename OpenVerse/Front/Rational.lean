/-
  OpenVerse front end — the helpers of `rational` (#116), written in Verse.

  A rational is, in Verse Core, the tuple (numerator, denominator) in lowest
  terms with a positive denominator, so tuple equality is rational equality.
  `X / Y` calls `$ratMake`, which divides by a gcd of either sign (Euclid
  with the Euclidean `Mod`), then makes the denominator positive: it
  overflows only when the result's numerator or denominator is out of
  range. An ordering
  `A < B` calls `$ratLt`, which compares two rationals by their continued
  fractions: every number it computes is bounded by the operands' parts, so
  it never overflows (cross multiplication would). The elaborator adds these definitions to a program
  that may use rationals (its source has `/` or `rational`).
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The helpers' names, and their parameters' and locals' (which must not
    collide with a program's definitions): each becomes `$name`, which no
    program can write. -/
def ratNames : List String :=
  ["ratGcd", "ratMake", "ratLt", "A", "B", "D", "G", "N", "P", "Q", "R", "S", "X", "Y",
   "Less", "Q1", "Q2", "R1", "R2"]

def ratPrelude : String := "
ratGcd(A:int, B:int)<computes>:int =
    var X:int = A
    var Y:int = B
    loop:
        if (R := Mod[X, Y]):
            set X = Y
            set Y = R
        else:
            break
    X

ratMake(N:int, D:int)<computes><decides>:tuple(int, int) =
    D <> 0
    G := ratGcd(N, D)
    P := Quotient[N, G]
    Q := Quotient[D, G]
    if (Q < 0) then (-P, -Q) else (P, Q)

ratLt(A:tuple(int, int), B:tuple(int, int))<computes><decides>:void =
    var P:int = A(0)
    var Q:int = A(1)
    var R:int = B(0)
    var S:int = B(1)
    var Less:logic = false
    loop:
        if (Q1 := Floor(P / Q), Q2 := Floor(R / S), R1 := Mod[P, Q], R2 := Mod[R, S]):
            if (Q1 <> Q2):
                if (Q1 < Q2) then set Less = true
                break
            if (R1 = 0):
                if (R2 <> 0) then set Less = true
                break
            if (R2 = 0) then break
            set P = S
            set R = Q
            set Q = R2
            set S = R1
        else:
            break
    Less?
"

/-- The helpers, parsed (their names renamed). -/
def ratTops : Except String (List STop) := parsePrelude ratPrelude ratNames

end OpenVerse.Front
