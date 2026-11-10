# Overloaded functions with several values (#283), effects and rollback across the chosen overload, one overload with one value
# (tim-61's expectations, written before the code)
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Pick(N:int)<transacts>:int = Tell("i{N}", N) | Tell("j{N}", N + 1)
Pick(S:string)<transacts>:int = Tell("s{S}", 7)
Main()<transacts>:void =
    for (X := 1 | 2, Y := Pick(X), Y > 2) { Print("x {Y}") }
    for (S := "a" | "b", Y := Pick(S)) { Print("y {Y}") }
