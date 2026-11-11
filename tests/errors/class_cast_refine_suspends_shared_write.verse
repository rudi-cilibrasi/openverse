# expect: cannot suspend while it captures the var 'Value' shared with a background task
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    branch:
        Sleep(0.5)
        Print("observed {Value}")
    if (D := dup[P]):
        set Value = 7
        Sleep(1.0)
Main()<suspends>:void =
    Run(dup(int){A := 1, B := 2})
