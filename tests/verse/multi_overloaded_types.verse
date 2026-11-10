# Overloaded functions with several values (#283), chosen by the arguments' types, an argument bound by an earlier clause, first success
# (tim-61's expectations, written before the code)
Two(N:int):int = N | N * 10
Two(S:string):int = S.Length | 100
Main():void =
    for (X := Two(3)) { Print("a {X}") }
    for (X := Two("ab")) { Print("b {X}") }
    for (X := 1, Y := Two(X)) { Print("c {Y}") }
    if (Y := Two("xyz"), Y > 50) then Print("d {Y}") else Print("none")
