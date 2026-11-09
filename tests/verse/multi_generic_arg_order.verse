# arguments of inlined calls, generic or not, and of a lazily taken one, evaluated in order, each once, before a later argument's choice (#235, review of #282)
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Two(A:int, B:int):int = A | B
Pick(X:t, Y:t where t:type):t = X | Y
Upto(Lo:int, Hi:int)<transacts><decides>:int =
    Lo <= Hi
    Lo | Upto[Lo + 1, Hi]
Main():void =
    for (X := Two(Tell("a", 1), Tell("b", 2) + (0 | 10))) { Print("{X}") }
    Print("--")
    for (X := Pick(Tell("c", 1), Tell("d", 2) + (0 | 10))) { Print("{X}") }
    Print("--")
    for (X := Upto[Tell("e", 1), 1 + (0 | 1)]) { Print("{X}") }
