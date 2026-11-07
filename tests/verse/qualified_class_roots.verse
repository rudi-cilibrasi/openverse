# qualified implementations of class roots, and a default a superclass
# inherits implementing an interface a subclass adds (#70)

a := class<abstract>:
    M():int
i1 := interface:
    M():int
c := class(a, i1):
    (i1:)M<override>():int = 1
    (a:)M<override>():int = 2
d := class(c):
    (a:)M<override>():int = 20 + (super:)M()

i := interface:
    N():int = 7
j := interface:
    N():int
b := class(i):
    V:int = 0
e := class(b, j):
    W:int = 0

Main():void =
    X:a = d{}
    Y:i1 = d{}
    Z := d{}
    Print("{X.M()} {Y.M()} {Z.(a:)M()} {Z.(i1:)M()}")
    J:j = e{}
    I:i = e{}
    Print("{J.N()} {I.N()} {e{}.N()}")
