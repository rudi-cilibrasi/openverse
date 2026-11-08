# a <suspends> method dispatched under the refinement of a class that
# repeats type arguments (#171, #209)
pair(t:type, u:type) := class:
    A:t
    B:u
    Get()<suspends>:t =
        Sleep(0.1)
        A
dup(t:type) := class(pair(t, t)):
    Get<override>()<suspends>:t =
        Sleep(0.2)
        B
Both(P:pair(t, u), Q:pair(t, u) where t:type, u:type)<suspends>:tuple(t, t) =
    X := P.Get()
    Y := Q.Get()
    (X, Y)
Main()<suspends>:void =
    R := Both(pair(int, int){A := 1, B := 2}, dup(int){A := 3, B := 4})
    Print("{R(0)} {R(1)}")
