# Classes with a class parent that add an interface at type arguments that
# are not a prefix of their own (#351), as the review found them: one that
# inherits its parent's implementation, dispatched to from a sink(int) with a
# pinned class beside it (tested apart from its parent, whose Verse Core
# pins differ); an interface with more type arguments than the class
# (keyed(string, t)); and a class without type parameters adding a generic
# interface at closed ones
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
keyed(k:type, v:type) := interface:
    Look(K:k):v
i(a:type, b:type) := interface:
    M(X:a):b
p(t:type) := class(sink(t)):
    Put<override>(X:t):int = 1
q(u:type) := class(p(u), container(int)):
    Get<override>():int = 42
qq(u:type, t:type) := class(p(u)):
    Q():int = 0
r(a:type) := class(qq(a, a)):
    Q<override>():int = 1
kq(t:type) := class(p(t), keyed(string, t)):
    V:t
    Look<override>(K:string):t = V
w := class:
    W:int = 0
wq := class(w, i(int, string)):
    M<override>(X:int):string = "wq"
GL(X:keyed(k, v), K:k where k:type, v:type):v = X.Look(K)
Main():void =
    S:sink(int) = q(int){}
    C:container(int) = q(int){}
    Print("{S.Put(1)} {C.Get()} {r(int){}.Q()}")
    K:keyed(string, int) = kq(int){V := 3}
    Print("{K.Look("a")} {GL(K, "b")} {kq(int){V := 4}.Put(0)}")
    I:i(int, string) = wq{}
    Print(I.M(1))
