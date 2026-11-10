# Overridden methods with several values of generic classes (#283): a generic subclass's override, at two type arguments
# (tim-61's expectations, written before the code)
box(t:type) := class:
    X:t
    Y:t
    Get()<transacts>:t = X | Y
sbox(t:type) := class(box(t)):
    Get<override>()<transacts>:t = Y | X | Y
Main()<transacts>:void =
    Bs:[]box(int) = array{box(int){X := 1, Y := 2}, sbox(int){X := 3, Y := 4}}
    for (B : Bs, V := B.Get()) { Print("a {V}") }
    Ss:[]box(string) = array{sbox(string){X := "p", Y := "q"}}
    for (B : Ss, V := B.Get()) { Print("b {V}") }
