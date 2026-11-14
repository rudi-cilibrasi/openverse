# choices whose alternatives have several values, with effects in an alternative and after the choice, undone with rejected values; a generator with effects after them (#283)
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
A():int = 1 | 2
Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
Main():void =
    if (X := Tell("t", 1) | A(), Print("after {X}"), X > 1) then Print("if {X}")
    Print("--")
    for (X := A() | Tell("u", 7), (Print("f {X}"); true?), X <> 2) { Print("body {X}") }
    Print("--")
    if (X := A() | 10, Y := Nat[0], X + Y > 11) then Print("nat {X} {Y}")
