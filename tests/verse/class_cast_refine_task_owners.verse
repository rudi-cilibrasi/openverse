# Lifted background tasks retain their source scope and cleanup order.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)) {}
After(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 0
    defer: Print("after source defer {X}")
    if (D := dup[P]):
        defer: Print("after cast defer {X}")
        set X = 7
        branch:
            defer: Print("after child defer {X}")
            Sleep(0.5)
            set X = 11
            Print("after child woke {X}")
    Print("after cast {X}")
    Sleep(1.0)
    Print("after wait {X}")
NoWait(P:pair(a, b) where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        defer: Print("no-wait cast defer")
        branch:
            defer: Print("no-wait child defer")
            Print("no-wait child")
    Print("no-wait source")
ElseNoWait(P:pair(a, b) where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        Print("else typed")
    else:
        branch: Print("else branch")
    Print("else source")
NestedNoWait(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    if (D := dup[P]):
        if (E := dup[Q]):
            branch: Print("nested no-wait child")
    Print("nested no-wait source")
Order(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 0
    defer:
        set X = 8
        Print("order source defer {X}")
    branch:
        defer: Print("order before {X}")
        Sleep(10.0)
    if (D := dup[P]):
        defer: Print("order cast defer {X}")
        branch:
            defer: Print("order first {X}")
            Sleep(10.0)
        rush:
            block:
                defer: Print("order rush {X}")
                Sleep(10.0)
            Sleep(0.01)
        branch:
            defer: Print("order last {X}")
            Sleep(10.0)
    set X = 7
    branch:
        defer: Print("order after {X}")
        Sleep(10.0)
    Print("order source end")
Cancel(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var X:int = 0
    defer:
        set X = 8
        Print("cancel source defer {X}")
    branch:
        defer: Print("cancel before {X}")
        Sleep(10.0)
    if (D := dup[P]):
        defer: Print("cancel cast defer {X}")
        branch:
            defer: Print("cancel child {X}")
            Sleep(10.0)
        set X = 7
        Sleep(10.0)
Return(P:pair(a, b) where a:type, b:type)<suspends>:int =
    var X:int = 0
    defer:
        set X = 9
        Print("return source defer {X}")
    if (D := dup[P]):
        defer:
            set X = 8
            Print("return cast defer {X}")
        branch:
            defer: Print("return child {X}")
            Sleep(10.0)
        set X = 7
        Sleep(0.01)
        return X
    -1
Nested(P:pair(a, b), Q:pair(c, d) where a:subtype(comparable), b:subtype(comparable), c:type, d:type)<suspends>:void =
    var X:int = 0
    if (D := dup[P]):
        var Y:a = D.A
        if (E := dup[Q]):
            branch:
                Sleep(0.25)
                set X = 9
                set Y = D.B
                if (Y = D.B):
                    Print("nested task changed both frames")
    Sleep(0.5)
    Print("nested source {X}")
Tree(P:pair(a, b) where a:type, b:type)<suspends>:void =
    defer: Print("tree source defer")
    if (D := dup[P]):
        branch:
            defer: Print("tree parent")
            Sleep(0.25)
            branch:
                defer: Print("tree child")
                Sleep(10.0)
            Sleep(10.0)
    branch:
        defer: Print("tree after")
        Sleep(10.0)
    Sleep(0.5)
Ordinary()<suspends>:void =
    branch:
        defer: Print("ordinary child cleanup")
        Sleep(10.0)
    Sleep(0.01)
    Print("ordinary return")
OrdinaryCaller(P:pair(a, b) where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        Ordinary()
        Print("after ordinary call")
Reuse(P:pair(a, b), N:int where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        branch:
            Sleep(0.1)
            Print("reuse {N}")
    Sleep(0.2)
expr(t:type) := class {}
parts(a:type, b:type) := class(expr(tuple(a, b))):
    L:a
    R:b
Opened(E:expr(t), Initial:t where t:type)<suspends>:t =
    var X:t = Initial
    if (P := parts[E]):
        branch:
            defer: Print("opened child defer")
            Sleep(0.25)
            set X = (P.L, P.R)
            Print("opened child woke")
    Sleep(0.5)
    X
holder(t:type) := class:
    var V:t
OpenedCancel(E:expr(t), H:holder(t) where t:type)<suspends>:void =
    var X:t = H.V
    defer: Print("opened source cancelled")
    if (P := parts[E]):
        branch:
            defer:
                set X = (P.L, P.R)
                set H.V = X
                Print("opened child cancelled")
            Sleep(10.0)
    Sleep(10.0)
Main()<suspends>:void =
    After(dup(int){A := 1, B := 2})
    After(pair(int, string){A := 1, B := "b"})
    NoWait(dup(int){A := 1, B := 2})
    NoWait(pair(int, string){A := 1, B := "b"})
    ElseNoWait(dup(int){A := 1, B := 2})
    ElseNoWait(pair(int, string){A := 1, B := "b"})
    NestedNoWait(dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"})
    Order(dup(int){A := 1, B := 2})
    race:
        Cancel(dup(int){A := 1, B := 2})
        block:
            Sleep(1.0)
            Print("cancel winner")
    Print("return operand {Return(dup(int){A := 1, B := 2})}")
    Nested(dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"})
    Tree(dup(int){A := 1, B := 2})
    OrdinaryCaller(dup(int){A := 1, B := 2})
    for (I := 1..2):
        Reuse(dup(int){A := 1, B := 2}, I)
    R := Opened(parts(int, string){L := 4, R := "opened"}, (0, "initial"))
    Print("opened source {R(0)} {R(1)}")
    H := holder(tuple(int, string)){V := (0, "initial")}
    race:
        OpenedCancel(parts(int, string){L := 8, R := "cancelled"}, H)
        Sleep(0.5)
    Print("opened cancelled value {H.V(0)} {H.V(1)}")
