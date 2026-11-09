# a refining cast as the first clause of an if's condition, a clause after it using it (#243 follow-up)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P], D.C > 0) then X else P.B
Main():void = Print("{F(dup(int){A := 1, B := 2}, 3)}")
