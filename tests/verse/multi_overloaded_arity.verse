# Overloaded functions with several values (#283), by arity
# (tim-61's expectations, written before the code)
F(A:int):int = A | -A
F(A:int, B:int):int = A + B
Main():void =
    for (X := F(5)) { Print("a {X}") }
    for (X := F(5, 1)) { Print("b {X}") }
    for (X := F(2), Y := F(X, 10)) { Print("c {Y}") }
