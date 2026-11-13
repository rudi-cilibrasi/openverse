# (#351) a cast to an interface beside the object's, neither above nor below
# it, also through views: a test of each class below both; the type
# arguments the interfaces above both relate to the object's are known,
# the others opened
named := interface:
    Name():string
container(t:type) := interface(named):
    Get():t
sink(u:type) := interface(named):
    Put(X:u):string
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Name<override>():string = "both"
    Get<override>():t = V
    Put<override>(X:u):string = "put"
c := class(container(int), sink(string)):
    Name<override>():string = "c"
    Get<override>():int = 7
    Put<override>(X:string):string = "c got {X}"
d := class(sink(string)):
    Name<override>():string = "d"
    Put<override>(X:string):string = "d got {X}"
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    B():t
ci := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>():string = "seven"
Twice(X:t where t:type):[]t = array{X, X}
# sink(string) to container: its type argument opened (t' is int for a c,
# whatever a both's is), so the branch passes it on to generic code only
Gets(S:sink(string)):int =
    if (C := container[S]) then Twice(C.Get()).Length + 10 else 0
# from code generic over the sink's own type argument
Puts(S:sink(u), X:u where u:type):string =
    if (C := container[S], N := C.Name()) then "{N}: {S.Put(X)}" else "not a container"
# from named, which has no type arguments, to sink, then to the beside one
Names(N:named):string =
    if (S := sink[N], C := container[S]) then "both {C.Name()}" else if (S := sink[N]) then "sink {S.Name()}" else "neither"
Main():void =
    Print("{Gets(c{})} {Gets(both(float, string){V := 1.5})} {Gets(d{})}")
    Print(Puts(c{}, "x"))
    Print(Puts(both(int, int){V := 1}, 3))
    Print(Puts(d{}, "y"))
    Print(Names(c{}))
    Print(Names(d{}))
    I:i2(string) = ci{}
    if (J := i1[I]) then Print("i1") else Print("not i1")
