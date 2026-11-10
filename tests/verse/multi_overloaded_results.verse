# Overloaded functions with several values (#283), with different result types, an argument that is a choice
# (tim-61's expectations, written before the code)
Two(N:int):int = N | N * 10
Two(S:string):string = S | "{S}{S}"
Main():void =
    for (X := Two(1 | 2)) { Print("a {X}") }
    for (X := Two("q")) { Print("b {X}") }
    for (S := "u" | "v", T := Two(S), T <> "vv") { Print("c {T}") }
