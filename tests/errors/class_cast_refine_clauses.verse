# expect: 8:16: cannot cast a pair(a, b) to dup(a) here: their type arguments agree only under a refinement, which a cast gives only as the whole condition of an if, D := dup[X], whose branch is then typed under it (#209, #243)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P], D.C > 0) then X else P.B
Main():void = Print("{F(dup(int){A := 1, B := 2}, 3)}")
