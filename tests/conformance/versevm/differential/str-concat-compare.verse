# String concatenation and equality, empty strings included.
# Tests LANGUAGE.md, Types: "string (= []char)"; Operators: "= and <> of any
# two comparable types, by value". Each letter: y the comparison succeeded,
# n it failed.
# OpenVerse prints (Lean and C agree):
#   cat abcd ab 4 6 | eq y y y y n
Main():void =
    A:string = "ab"
    B:string = A + "cd"
    C:string = "" + A + ""
    Print("OVPROBE cat {B} {C} {B.Length} {(A + A + A).Length}")
    P := if (B = "abcd") then "y" else "n"
    Q := if (A <> "abc") then "y" else "n"
    R := if (C = A) then "y" else "n"
    S := if ("" = "") then "y" else "n"
    T := if ("a" = "A") then "y" else "n"
    Print("OVPROBE eq {P} {Q} {R} {S} {T}")
