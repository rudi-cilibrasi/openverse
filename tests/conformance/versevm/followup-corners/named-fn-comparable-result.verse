# followup-corners (#724): A function with a <unique> class result,
# MakeToken():token, named where a function with a comparable result is
# expected, its two results compared. (followup-variance/comparable-result
# asks it of a function value.)
# OpenVerse (Lean and C agreeing): refused, expected type{_():comparable},
# found type{_():token}.
# If Epic refuses it, OpenVerse agrees on the verdict. If it admits it and
# prints value different (two objects), a function named converts to a
# comparable result as it does to an any result: OpenVerse would convert it.
# Not yet compiled or run by UEFN.
token := class<unique> {}

MakeToken():token = token{}

RunComparable(F():comparable):string =
    A := F()
    B := F()
    if (A = B) then "same" else "different"

Main():void =
    Print("OVPROBE value {RunComparable(MakeToken)}")
