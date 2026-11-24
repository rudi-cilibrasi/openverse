# As choice_interpolation_overflow_before_call, with an if that picks a
# branch with a choice in the next value, whose conditions are lifted before
# the string, and the big int in a name (#723): the overflow error comes
# first, so "c" is not printed.
Big(X:int)<transacts>:int = 9223372036854775807 + X
Main():void =
    Print("start")
    B := Big(1)
    for (T := "<{B}-{(if (Print("c"), 1 = 1) then (2 | 4) else 3)}>") { Print(T) }
    Print("not reached")
