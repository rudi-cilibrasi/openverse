# A cast of a reference through views to a class with type arguments takes
# them from a dispatch (#351), also as a later clause of an if's condition
# after one that prints: the cast takes the clauses after it as its branch,
# and the then-branch, which uses its name, casts again (#243). The Print
# stays, as the cast succeeds.
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
one(u:type) := class(sink(u)):
    W:u
    Put<override>(X:u):int = 100
Main():void =
    S:sink(string) = one(string){W := "w"}
    if (Print("t"), O := one[S]) then Print("one {O.W}") else Print("not one")
