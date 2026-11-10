# Defaults through a view (#351): one computed by code that another uses, ?K := M with ?M := C.Next(), stored
# where it is in the call and read there, so it runs once, as in a direct call
ctr := class:
    var N:int = 0
    Next()<transacts>:int =
        set N = N + 1
        N
sink(u:type) := interface:
    A(C:ctr, X:u, ?M:int = 0, ?K:int = 0)<transacts>:int
both(t:type, u:type) := class(sink(u)):
    V:t
    A<override>(C:ctr, X:u, ?M:int = C.Next(), ?K:int = M)<transacts>:int = M * 10 + K
Main()<transacts>:void =
    S:sink(string) = both(int, string){V := 1}
    D := both(int, string){V := 1}
    C1 := ctr{}
    C2 := ctr{}
    Print("view {S.A(C1, "x")} direct {D.A(C2, "x")}")
