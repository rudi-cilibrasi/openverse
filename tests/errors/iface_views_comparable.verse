# expect: type parameter w of both.Eq2 must be comparable, and x is not: declare x:subtype(comparable)
# a dispatch through a view opens the class's type arguments each as
# comparable as its type parameter, and keeps the caller's names: x, not
# comparable, cannot be w, which must be
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Eq2(Y:w, Z:w where w:subtype(comparable)):logic
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Eq2<override>(Y:w, Z:w where w:subtype(comparable)):logic = if (Y = Z) then true else false
G(S:sink(x), A:x where x:type):logic = S.Eq2(A, A)
Main():void =
    B := both(int, string){V := 3}
    if (G(B, "a")?) then Print("eq") else Print("ne")
