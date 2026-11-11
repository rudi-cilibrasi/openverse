pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    rush:
        block:
            Sleep(0.5)
            set Value = 7
            ()
        Sleep(0.0)
    if (D := dup[P]):
        Sleep(1.0)
        Print("observed {Value}")
Main()<suspends>:void =
    Run(dup(int){A := 1, B := 2})
