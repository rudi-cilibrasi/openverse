# followup-variance (#724): Does UEFN 43.12 admit comparable as the
# supertype of a parameter: a local of type type{_(:comparable):int} passed
# where a type{_(:token):int} is expected, token a <unique> class
# (comparable, its value its own box)? Epic admits followup-coerce's
# value-class-variance and followup-coerce2's value-class-result, a class
# parameter and a class result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse refuses it: expected type{_(:token):int}, found
# type{_(:comparable):int} (a function named there is refused too).
# If Epic refuses it (3502), OpenVerse agrees but for the error number. If
# it admits it and prints value 6, a unique class converts to comparable as
# it is in a function value's parameter: OpenVerse would make that
# conversion (a unique object is its own box), and likewise for a function
# named there.
token := class<unique> {}

TakeComparable(X:comparable):int = 6
RunToken(F(:token):int):int = F(token{})

Main():void =
    G:type{_(:comparable):int} = TakeComparable
    Print("OVPROBE value {RunToken(G)}")
