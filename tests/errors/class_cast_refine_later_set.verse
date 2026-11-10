# expect: 10:27: cannot cast a pair(a, b) to dup(a) here
# (#243: the var set before the cast would keep its value when the cast fails, which undoes the whole condition)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b) where a:type, b:type)<transacts>:int =
    var V:int = 0
    if (set V = 5, D := dup[P]):
        Print("then V={V}")
    else:
        Print("else V={V}")
    V
Main()<transacts>:void =
    Print("{F(dup(int){A := 1, B := 2, C := 3})}")
    Print("{F(pair(int, string){A := 1, B := "x"})}")
