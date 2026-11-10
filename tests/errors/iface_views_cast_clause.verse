# expect: works only as the first clause of an if's condition, D := one[X], whose branch then has one's type arguments (#351)
# a cast of a reference through views to a class with type arguments takes
# them from a dispatch, which only a cast that is the first clause of an
# if's condition makes
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
