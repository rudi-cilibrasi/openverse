# a generator followed, where the first success is taken, by a choice, a generator or an eager recursive call that all fail for its first value: what that value's clauses did is undone (#246, review of #267)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Tri(N:int)<computes><decides>:int =
    N > 0
    Upto[1, N] | Tri[N - 1]
Main():void =
    if (X := Upto[1, 2], Print("a {X}"), Y := 1 | 2, X + Y = 4) then Print("found {X} {Y}")
    if (X := 1 | 2, Print("b {X}"), Y := Upto[1, 2], X + Y = 4) then Print("found {X} {Y}")
    if (X := Upto[1, 2], Print("c {X}"), Y := Tri[1], X + Y = 3) then Print("found {X} {Y}")
    if (X := Upto[1, 2], Print("d {X}"), Y := Upto[1, 2], Z := Upto[1, 2], X + Y + Z = 6) then Print("found {X}{Y}{Z}")
