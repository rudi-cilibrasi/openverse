# interfaces whose type arguments are not a prefix of a class's (#351):
# references to sink go through views (both's view of sink is its second type
# argument), as do references to the interface above it (named); generic code
# over sink(x) dispatches through the view; casts come back; a subclass
# overrides; c gives two interfaces different closed type arguments
named := interface:
    Name():string
container(t:type) := interface:
    Get():t
sink(u:type) := interface(named):
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    var N:int = 0
    Get<override>():t = V
    Put<override>(X:u):int =
        set N += 1
        N
    Name<override>():string = "both"
one(u:type) := class(sink(u)):
    Put<override>(X:u):int = 100
    Name<override>():string = "one"
loud(t:type, u:type) := class(both(t, u)):
    Put<override>(X:u):int = 1000
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    B():t
c := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>():string = "seven"
GS(S:sink(x), V:x where x:type):int = S.Put(V)
GN(Ns:[]named):[]string = for (N : Ns) { N.Name() }
GB(I:i2(y) where y:type):y = I.B()
Main():void =
    B := both(int, string){V := 3}
    Print("{GS(B, "a")} {GS(B, "b")} {B.N}")
    Ss:[]sink(string) = array{B, one(string){}, loud(float, string){V := 1.5}}
    for (S : Ss) { Print("put {S.Put("x")} {S.Name()}") }
    for (S : Ss):
        if (D := both[S]) then Print("both {D.N}") else Print("not both")
    Cs:[]container(int) = array{B, both(int, float){V := 4}}
    for (C : Cs) { Print("get {C.Get()}") }
    for (Nm : GN(array{B, one(int){}})) { Print("named {Nm}") }
    K := c{}
    Print("{GB(K)} {K.A()}")
