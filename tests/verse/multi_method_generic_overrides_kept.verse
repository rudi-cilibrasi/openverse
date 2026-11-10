# Overridden methods with several values of generic classes (#283): a method with several values of a
# generic subclass that calls the overridden one (Self's, plain or bound first), whose own body is checked
# apart from its calls with the receiver at the declaring class (tim-61's review case g7)
box(t:type) := class:
    X:t
    Y:t
    Get()<transacts>:t = X | Y
up(t:type) := class(box(t)):
    Get<override>()<transacts>:t = Y | Y
mid(t:type) := class(box(t)):
    Use()<transacts>:t = Get()
    Use2()<transacts>:t = Self.Get()
    Use3()<transacts>:t =
        V := Get()
        V
Main()<transacts>:void =
    M := mid(int){X := 1, Y := 2}
    for (V := M.Get()) { Print("m {V}") }
    for (V := M.Use()) { Print("u {V}") }
    U := up(string){X := "a", Y := "b"}
    for (V := U.Get()) { Print("p {V}") }
    for (V := M.Use2()) { Print("s {V}") }
    for (V := M.Use3()) { Print("f {V}") }
