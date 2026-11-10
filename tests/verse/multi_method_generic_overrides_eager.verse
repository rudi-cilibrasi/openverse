# Overridden methods with several values of generic classes (#283), reached from a recursive <computes>
# function whose values are computed at the call (F$all), at a fixed type argument and at its own
box(t:type) := class:
    X:t
    Y:t
    Get()<computes>:t = X | Y
up(t:type) := class(box(t)):
    Get<override>()<computes>:t = Y | X
Walk(B:box(int), N:int)<computes>:int = if (N > 0) then Walk(B, N - 1) else B.Get()
Walk2(B:box(t), N:int where t:type)<computes>:t = if (N > 0) then Walk2(B, N - 1) else B.Get()
Main()<transacts>:void =
    Bs : []box(int) = array{box(int){X := 1, Y := 2}, up(int){X := 3, Y := 4}}
    for (B : Bs, V := Walk(B, 2)) { Print("w {V}") }
    for (B : Bs, V := Walk2(B, 2)) { Print("v {V}") }
    S : box(string) = up(string){X := "a", Y := "b"}
    for (V := Walk2(S, 1)) { Print("s {V}") }
