# expect: cannot suspend while it sets the var 'Value' used by an enclosing defer
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    defer: Print("cleanup {Value}")
    if (D := dup[P]):
        set Value = 7
        Sleep(2.0)
Main()<suspends>:void =
    race:
        Run(dup(int){A := 1, B := 2})
        Sleep(1.0)
