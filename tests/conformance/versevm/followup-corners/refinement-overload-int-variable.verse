# followup-corners (#724): Two overloads on disjoint refinements of int
# (followup-refused/refinement-overloads, which UEFN admits and runs with
# literals), called with an int parameter that is no literal: F(N), N:int.
# OpenVerse (Lean and C agreeing): refused, no overload of F takes (int) (a
# call takes the overload its argument's type is of when compiled; an int is
# of neither without a cast).
# If Epic refuses it (3509), OpenVerse agrees. If it admits it and prints
# negative 0 small 1, the overload is chosen by the value when run:
# OpenVerse would dispatch on the value (and what an int in neither interval
# does would be the next question).
# Not yet compiled or run by UEFN.
small := type{_X:int where 0 <= _X, _X < 65535}
negative := type{_X:int where _X < 0}

F(X:small):int = X
F(X:negative):int = X + 1

Call(N:int):int = F(N)

Main():void =
    Print("OVPROBE negative {Call(-1)} small {Call(1)}")
