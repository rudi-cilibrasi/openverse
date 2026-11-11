pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        branch:
            Sleep(1.0)
            Print("child woke")
        Sleep(0.0)
    Sleep(2.0)
Main()<suspends>:void =
    Run(dup(int){A := 1, B := 2})
