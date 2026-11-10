# Defaults through a view (#351): ?B := A * 2 with A computed by code, evaluated once (tim-61's q7)
Tell(S:string, V:int)<transacts>:int =
    Print(S)
    V
container(t:type) := interface:
    Get()<transacts>:t
sink7(u:type) := interface:
    P7(X:u, ?A:int = Tell("da", 1), ?B:int = A + 1)<transacts>:int
both7(t:type, u:type) := class(container(t), sink7(u)):
    V:t
    Get<override>()<transacts>:t = V
    P7<override>(X:u, ?A:int = Tell("ea", 10), ?B:int = A * 2)<transacts>:int = A + B
Main()<transacts>:void =
    R:sink7(string) = both7(int, string){V := 1}
    Print("m {R.P7("x")}")
    Print("m {R.P7("x", ?A := 3)}")
