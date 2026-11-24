# (#723) A for over a function that runs a for over a call of itself before its flat
# choice: the bodies the inner for ran commit nothing of the outer search. A row of the
# outer for that reaches no body is rolled back whole, the argument's and the inner
# for's output with it (Epic's Verse VM labels such lines "(Rolling Back)":
# tests/conformance/versevm/followup-print, print-for-filter); one that reaches the body
# keeps them. The generic function and the one written at int agree.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
P(X:t, Y:t, N:int where t:type)<transacts><decides>:t =
    N > 0
    var C:int = 0
    for (Z := P[Y, X, N - 1]) { set C += 1 }
    Print("P {N} {C}")
    X | Y
Q(X:int, Y:int, N:int)<transacts><decides>:int =
    N > 0
    var C:int = 0
    for (Z := Q[Y, X, N - 1]) { set C += 1 }
    Print("Q {N} {C}")
    X | Y
Main()<transacts>:void =
    for (V := P[2, 5, Tell("p none", 1)], V > 7) { Print("{V}") }
    Print("--")
    for (V := P[2, 5, Tell("p nested none", 3)], V > 7) { Print("{V}") }
    Print("--")
    for (V := P[2, 9, Tell("p second", 3)], V > 7) { Print("{V}") }
    Print("--")
    for (V := P["a", "b", Tell("p all", 2)]) { Print(V) }
    Print("--")
    for (V := Q[2, 5, Tell("q none", 1)], V > 7) { Print("{V}") }
    Print("--")
    for (V := Q[2, 5, Tell("q nested none", 3)], V > 7) { Print("{V}") }
    Print("--")
    for (V := Q[2, 9, Tell("q second", 3)], V > 7) { Print("{V}") }
    Print("--")
    if (V := P[2, 5, Tell("p if", 2)], V > 7) then Print("{V}") else Print("p if none")
    if (V := P[2, 9, Tell("p if", 2)], V > 7) then Print("{V}") else Print("p if none")
