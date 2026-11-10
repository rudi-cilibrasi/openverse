# Computed named defaults through a view (#351), from #397's review: a chain of defaults that use the ones
# before them (a literal, an alias, a computed one at the end)
Tick(S:string)<transacts>:int =
    Print("tick {S}")
    7
sink(u:type) := interface:
    A(X:u, ?M:int = Tick("m"), ?K:int = M)<transacts>:int
    B(X:u, ?P:int = 3, ?Q:int = P, ?R:int = Tick("r") + Q)<transacts>:int
both(t:type, u:type) := class(sink(u)):
    V:t
    A<override>(X:u, ?M:int = Tick("m"), ?K:int = M)<transacts>:int = M + K
    B<override>(X:u, ?P:int = 3, ?Q:int = P, ?R:int = Tick("r") + Q)<transacts>:int = P + Q + R
Main()<transacts>:void =
    S := both(int, string){V := 1}
    Print("a {S.A("x")}")
    Print("b {S.B("x")}")
