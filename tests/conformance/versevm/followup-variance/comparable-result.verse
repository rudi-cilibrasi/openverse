# followup-variance (#724): Does UEFN 43.12 admit comparable as the
# supertype of a result: a local of type type{_():token} used as a
# type{_():comparable}, token a <unique> class, its two results compared?
# Epic admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse refuses it: expected type{_():comparable}, found type{_():token}
# (a function named there is refused too).
# If Epic refuses it (3502), OpenVerse agrees but for the error number. If
# it admits it and prints value different (two objects), a unique class
# converts to comparable as it is in a function value's result: OpenVerse
# would make that conversion, and likewise for a function named there.
token := class<unique> {}

MakeToken():token = token{}
RunComparable(F():comparable):string =
    A := F()
    B := F()
    if (A = B) then "same" else "different"

Main():void =
    G:type{_():token} = MakeToken
    Print("OVPROBE value {RunComparable(G)}")
