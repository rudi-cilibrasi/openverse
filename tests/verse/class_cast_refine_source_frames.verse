# Mutable captures refer to their source frame across waits and cancellation.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)) {}
BothWays(P:pair(a, b), Unused:t where a:type, b:type, t:type)<suspends>:void =
    var X:int = 0
    var Copy:int = X
    branch:
        Sleep(0.5)
        Print("background {X}")
        set X = 3
    if (D := dup[P]):
        set X = 7
        Saved := X
        Sleep(1.0)
        Print("lift {X} saved {Saved} copy {Copy}")
        set X = 9
    Print("source {X}")
Cancel(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 0
    defer: Print("source defer {X}")
    if (D := dup[P]):
        defer:
            Print("lift defer {X}")
            set X = 8
        set X = 7
        Sleep(2.0)
Nested(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:tuple(a, a) =
    var X:a = P.A
    Result := if (D := dup[P]):
        var Y:a = D.A
        if (E := dup[Q]):
            set X = D.B
            set Y = D.B
            Sleep(0.01)
        Y
    else:
        P.A
    (X, Result)
Condition(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 0
    branch:
        Sleep(0.5)
        Print("condition background {X}")
    if (set X = 1, V := if (D := dup[P]) then (X | X) else 0, V = 1):
        Print("condition read {X}")
    if (set X = 2, V := if (D := dup[P]) then X else 0, V = 0):
        Print("unreachable")
    else:
        Print("condition rollback {X}")
    Sleep(1.0)
Sink(N:int)<suspends>:void = Print("spawn argument {N}")
SpawnArg(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 7
    T := spawn{Sink(if (D := dup[P]) then X else 0)}
    T.Await()
Scopes(P:pair(a, b) where a:type, b:type)<suspends>:void =
    block:
        var X:int = 1
        branch:
            Sleep(0.5)
            Print("first scope {X}")
        if (D := dup[P]):
            set X = 7
            Sleep(0.01)
    block:
        var X:int = 10
        if (D := dup[P]):
            set X = 9
            Sleep(0.01)
    Sleep(1.0)
ImmediateLocal(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    var X:int = 0
    branch:
        Sleep(0.5)
        Print("immediate background {X}")
    if (D := dup[P]):
        var Y:int = 0
        if (E := dup[Q]):
            set Y = 7
            set X = 5
        Print("immediate {Y} {X}")
    Sleep(1.0)
Main()<suspends>:void =
    BothWays(dup(int){A := 1, B := 2}, "unused witness")
    race:
        Cancel(dup(int){A := 1, B := 2})
        Sleep(1.0)
    R := Nested(dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"})
    Print("nested {R(0)} {R(1)}")
    Condition(dup(int){A := 1, B := 2})
    SpawnArg(dup(int){A := 1, B := 2})
    Scopes(dup(int){A := 1, B := 2})
    ImmediateLocal(dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"})
