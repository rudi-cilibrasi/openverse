# The empty value: an empty array, an empty option, an empty string and an
# empty map compared with false and with each other.
# Tests LANGUAGE.md, Equality and the empty value: "Verse has one empty
# value, written false or () (Book of Verse ch. 2 ...): it is the logic
# false, the value of void and tuple(), the empty option, and the empty
# array, string and map"; Readings, "= between different types". Epic's
# compiler may refuse comparisons across these types. Each letter: y the
# comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   y y y y y
Main():void =
    A:[]int = array{}
    O:?int = false
    S:string = ""
    M:[int]int = map{}
    P := if (A = false) then "y" else "n"
    Q := if (O = false) then "y" else "n"
    R := if (S = A) then "y" else "n"
    T := if (O = S) then "y" else "n"
    U := if (M = A) then "y" else "n"
    Print("OVPROBE {P} {Q} {R} {T} {U}")
