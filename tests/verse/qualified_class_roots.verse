# qualified implementations of class roots (#70), and a subclass that adds an
# interface implementing its method itself beside a default its superclass
# inherits (#724: the inherited default, from an interface that is not below
# j, does not implement j's N, UEFN 43.12 error 3591,
# followup-book2/final-method-interface)

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
    N<override>():int = 7

Main():void =
    X:a = d{}
    Y:i1 = d{}
    Z := d{}
    Print("{X.M()} {Y.M()} {Z.(a:)M()} {Z.(i1:)M()}")
    J:j = e{}
    I:i = e{}
    Print("{J.N()} {I.N()} {e{}.N()}")
