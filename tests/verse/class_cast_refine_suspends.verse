# A cast that refines (#243) in a <suspends> function, suspending around it
# but not in its branch or else.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type)<suspends>:b =
    Sleep(0.0)
    R := if (D := dup[P]) then X else P.B
    Sleep(0.0)
    R
Main()<suspends>:void =
    Print("{F(dup(int){A := 1, B := 2}, 7)} {F(pair(int, int){A := 1, B := 2}, 7)}")
