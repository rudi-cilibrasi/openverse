# Defaults through a view (#351), from #397's review: a tuple default with a part of no type of its own and
# a part using an earlier default (also as main had it wrong, (false, Q)), an array default another uses
Tick(S:string, N:int)<transacts>:int =
    Print("tick {S}")
    N
sink(u:type) := interface:
    A(X:u, ?Q:int = 1, ?P:tuple(?int, int) = (false, 0))<transacts>:int
both(t:type, u:type) := class(sink(u)):
    V:t
    A<override>(X:u, ?Q:int = 4, ?P:tuple(?int, int) = (false, Tick("p", Q)))<transacts>:int = P(1)
Main()<transacts>:void =
    S:sink(string) = both(int, string){V := 1}
    D := both(int, string){V := 1}
    Print("view {S.A("x")} direct {D.A("x")}")
