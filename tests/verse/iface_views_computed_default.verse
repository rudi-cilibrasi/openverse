# Named arguments' defaults computed by code, in calls through views (#351) and to classes that fix
# type arguments called from generic code (#142): each class's own default, evaluated in the call when
# that class is the receiver's (its effects only then), after the arguments before it, one using an
# earlier argument
Tick(S:string)<transacts>:int =
    Print("tick {S}")
    7
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u, ?N:int = Tick("i")):int
    Use(X:u, ?M:int = 5, ?K:int = M * 2)<transacts>:int
    Two(X:u, ?A:int = Tick("a"), ?B:int = Tick("b"))<transacts>:int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u, ?N:int = Tick("both")):int = N
    Use<override>(X:u, ?M:int = 5, ?K:int = M * 2)<transacts>:int = M + K
    Two<override>(X:u, ?A:int = Tick("a"), ?B:int = Tick("b"))<transacts>:int = A * 10 + B
one(u:type) := class(sink(u)):
    Put<override>(X:u, ?N:int = Tick("one") + 1):int = N
    Use<override>(X:u, ?M:int = 6, ?K:int = M * 3)<transacts>:int = M + K
    Two<override>(X:u, ?A:int = 1, ?B:int = Tick("b1"))<transacts>:int = A + B
Main()<transacts>:void =
    Ss:[]sink(string) = array{both(int, string){V := 1}, one(string){}}
    for (S : Ss):
        Print("put {S.Put("x")}")
        Print("put2 {S.Put("x", ?N := 3)}")
        Print("use {S.Use("x")} {S.Use("x", ?M := 1)}")
        Print("two {S.Two("x")}")
