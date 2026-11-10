# Interfaces referred to through views (#351), at the shapes the first
# review found: views at the places a class's chain gives them (a class
# below that fixes one, or adds one of its own), a slot's initial value,
# named arguments' defaults with no type of their own, casts down and from
# an interface above, and generic calls
container(t:type) := interface:
    Get():t
tagged(w:type) := interface:
    Tag():string
sink(u:type) := interface(tagged(u)):
    Put(X:u):int
    Opt(X:u, ?Alt:?u = false):u
    Arr(X:u, ?Pre:[]u = array{}):int
    Pair(X:u, ?K:tuple(int, int) = (1, 2)):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
    Opt<override>(X:u, ?Alt:?u = false):u = if (A := Alt?) then A else X
    Arr<override>(X:u, ?Pre:[]u = array{}):int = Pre.Length
    Pair<override>(X:u, ?K:tuple(int, int) = (3, 4)):int = K(0) + K(1)
    Tag<override>():string = "both"
# (sink's type argument is half's second, which it fixes to int)
half(t:type) := class(both(t, int)):
    Put<override>(X:int):int = X + 1
    Tag<override>():string = "half"
ib := class(both(int, string)):
    Put<override>(X:string):int = 2
    Tag<override>():string = "ib"
# (a type parameter of its own, after both's)
tri(a:type, t:type, u:type) := class(both(t, u)):
    Note:string = "n"
    Tag<override>():string = "tri"
one(u:type) := class(sink(u)):
    W:u
    Put<override>(X:u):int = 100
    Opt<override>(X:u, ?Alt:?u = false):u = X
    Arr<override>(X:u, ?Pre:[]u = array{}):int = Pre.Length + 100
    Pair<override>(X:u, ?K:tuple(int, int) = (5, 6)):int = K(0) * K(1)
    Tag<override>():string = "one"
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    B(X:t):t
c := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>(X:string):string = "seven"
d(t:type) := class(i1(int), i2(t)):
    K:int
    A<override>():int = K
    B<override>(X:t):t = X
e(t:type) := class(i2(t)):
    B<override>(X:t):t = X
GB(I:i2(y), V:y where y:type):y = I.B(V)
Main():void =
    S1:sink(string) = both(int, string){V := 1}
    S2:sink(int) = half(char){V := 'c'}
    S3:sink(string) = ib{V := 3}
    S4:sink(char) = tri(float, int, char){V := 3}
    Print("{S1.Put("x")} {S2.Put(5)} {S3.Put("y")} {S4.Put('z')} {S4.Tag()}")
    Ss:[]sink(string) = array{both(int, string){V := 3}, one(string){W := "w"}, ib{V := 4}}
    for (S : Ss):
        Print("{S.Opt("a")} {S.Opt("a", ?Alt := option{"b"})} {S.Arr("a")} {S.Arr("a", ?Pre := array{"x", "y"})} {S.Pair("a")}")
    for (S : Ss):
        if (O := one[S]) then Print("one {O.W}") else Print("not one")
        if (B := both[S]) then Print("both {B.Tag()}") else Print("not both")
    X:tagged(string) = both(int, string){V := 3}
    if (S := sink[X]) then Print("sink {S.Put("p")}") else Print("not sink")
    I:i2(int) = e(int){}
    Print("{I.B(1)}")
    D := d(string){K := 5}
    Print("{GB(D, "s")} {GB(c{}, "t")}")
    Is:[]i2(string) = array{c{}, d(string){K := 1}, e(string){}}
    for (J : Is):
        if (E := e[J]) then Print("e {E.B("q")}") else Print("not e")
