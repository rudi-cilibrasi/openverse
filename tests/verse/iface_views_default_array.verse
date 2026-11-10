# Defaults through a view (#351): an array default (no effect) that a later computed one uses, put in both
Tick(S:string, N:int)<transacts>:int =
    Print("tick {S}")
    N
sink(u:type) := interface:
    Put(X:u, Y:v, ?Z:[]v = array{Y}, ?N:int = 0 where v:type)<transacts>:int
both(t:type, u:type) := class(sink(u)):
    V:t
    Put<override>(X:u, Y:v, ?Z:[]v = array{Y, Y}, ?N:int = Tick("n", Z.Length) where v:type)<transacts>:int = Z.Length * 10 + N
Main()<transacts>:void =
    S:sink(string) = both(int, string){V := 1}
    D := both(int, string){V := 1}
    Print("view {S.Put("x", 1)} direct {D.Put("x", 1)}")
