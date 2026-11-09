# a refining cast as the first clause, whose else, written twice by the rewrite, has a refining cast too (#243 follow-up)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
trip(t:type) := class(pair(t, t)):
    D:int = 1
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P], D.C > 0) then X else (if (T := trip[P], T.D > 0) then X else P.B)
Main():void =
    Print("{F(dup(int){A := 1, B := 2}, 3)} {F(trip(int){A := 1, B := 2}, 3)} {F(pair(int, int){A := 1, B := 2}, 3)}")
