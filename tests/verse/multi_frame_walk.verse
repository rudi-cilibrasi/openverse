# A recursive function with several values whose call of itself has code
# after it (#283): taken lazily, the code a return frame that runs on each of
# the call's values, as part of that value. Values come in spatial order;
# what a value does (here, every frame's Print on its way out) is undone with
# it where the consumer rejects it, in a for's filter and where the first
# success is taken.
Walk(N:int)<transacts><decides>:int =
    N > 0
    X := Walk[N - 1] | N
    Print("at {N} got {X}")
    X + 1
Main()<transacts>:void =
    for (V := Walk[3]) { Print("v {V}") }
    Print("--")
    for (V := Walk[3], V > 4) { Print("never {V}") }
    Print("--")
    if (V := Walk[3], V > 4) then Print("first {V}") else Print("none")
    if (V := Walk[3], V >= 4) then Print("first {V}")
