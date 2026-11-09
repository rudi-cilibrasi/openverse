# expect: 8:24: cannot cast a pair(a, b) to dup(a) here: their type arguments agree only under a refinement, which a cast gives only as the first clause of an if's condition
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (Y := 1, D := dup[P], D.C > Y) then X else P.B
Main():void = Print("{F(dup(int){A := 1, B := 2}, 3)}")
