# qualified implementations by slot (#70): a method's slots are its root
# declarations; every static path to a slot reaches the same implementation

i1 := interface:
    M():int
i2 := interface:
    M():int

# a qualified implementation below a plain one wins in its slot
b := class(i1):
    M<override>():int = 1
c := class(b):
    (i1:)M<override>():int = 2

# a qualified implementation below an interface's default override
i := interface:
    N():int
j := interface(i):
    N<override>():int = 5
k := class(j):
    (i:)N<override>():int = 1

# one interface's default, the other qualified
d1 := interface:
    D():int = 10
d2 := interface:
    D():int = 20
e := class(d1, d2):
    (d1:)D<override>():int = 1

# (super:) in a qualified implementation: that slot's implementation above
f := class(i1, i2):
    M<override>():int = 3
g := class(f):
    (i1:)M<override>():int = 1
h := class(g):
    (i1:)M<override>():int = 10 + (super:)M()
    # a bare (i:)M is Self.(i:)M
    Both():int = (i1:)M() + (i2:)M()

# a qualified implementation after a field without a default, and after an
# abstract method
m := class<abstract>(i1, i2):
    V:int
    (i1:)M<override>():int = V
    W():int
    (i2:)M<override>():int = W()
n := class(m):
    W<override>():int = 7

Main():void =
    X:b = c{}
    A:i1 = c{}
    Y := c{}
    Print("{X.M()} {A.M()} {Y.M()} {Y.(i1:)M()}")
    J:j = k{}
    I:i = k{}
    Print("{J.N()} {I.N()}")
    D1:d1 = e{}
    D2:d2 = e{}
    Print("{D1.D()} {D2.D()}")
    H := h{}
    Print("{H.(i1:)M()} {H.(i2:)M()} {H.Both()}")
    Ns:[]i2 = array{n{V := 4}}
    for (Q : Ns) { Print("{Q.M()}") }
    Ms:[]i1 = array{n{V := 4}, c{}, H}
    for (Q : Ms) { Print("{Q.M()}") }
