# a value that sets a name its generator's clauses bind: the next alternative sees it as the value's iteration left it, kept or undone (#246)
Twice(N:int)<transacts><decides>:int =
    N > 0
    var K:int = 0
    (set K += 1; K) | (set K += 10; K) | Twice[N - 1]
Main():void =
    for (X := Twice[1]) { Print("all {X}") }
    for (X := Twice[1], X > 5) { Print("filtered {X}") }
    if (X := Twice[1], X > 5) then Print("first {X}")
