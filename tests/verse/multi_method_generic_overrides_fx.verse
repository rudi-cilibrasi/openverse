# Overridden methods with several values of generic classes (#283): effects and rollback through a generic family's dispatch
# (tim-61's expectations, written before the code)
Tell(S:string, V:t where t:type)<transacts>:t =
    Print(S)
    V
box(t:type) := class:
    X:t
    Y:t
    Get()<transacts>:t = Tell("bx", X) | Tell("by", Y)
tbox(t:type) := class(box(t)):
    Get<override>()<transacts>:t = Tell("tx", X) | Tell("ty", Y)
Main()<transacts>:void =
    Bs:[]box(int) = array{box(int){X := 1, Y := 2}, tbox(int){X := 3, Y := 9}}
    for (B : Bs, V := B.Get(), V > 2) { Print("d {V}") }
    if (B := Bs[1], V := B.Get(), V > 5) then Print("f {V}") else Print("none")
