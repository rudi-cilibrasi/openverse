# Refining casts in <suspends> functions (#243): the branch and the else suspending, a defer around the
# dispatch, calls from spawned tasks
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type)<suspends>:b =
    if (D := dup[P]):
        Sleep(1.0)
        Print("woke {D.C}")
        X
    else:
        Sleep(2.0)
        Print("else woke")
        P.B
G(P:pair(a, b) where a:type, b:type)<suspends>:void =
    defer: Print("g defer")
    if (D := dup[P]):
        Print("g before")
        Sleep(0.5)
        Print("g after {D.C}")
Main()<suspends>:void =
    V := F(dup(int){A := 1, B := 2, C := 5}, 7)
    Print("v {V}")
    W := F(pair(int, string){A := 1, B := "x"}, 7)
    Print("w {W}")
    G(dup(int){A := 1, B := 2, C := 3})
    T1 := spawn{ F(dup(int){A := 1, B := 2, C := 9}, 70) }
    T2 := spawn{ G(dup(int){A := 1, B := 2, C := 4}) }
    Print("t1 {T1.Await()}")
    T2.Await()
