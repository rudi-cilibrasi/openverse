# qualified implementations (i:)M: a class implementing two interfaces that
# declare the same method gives each its own; a call through an interface
# uses that interface's, and X.(i:)M() names one

i1 := interface:
    M():int
i2 := interface:
    M():int
    N():int = 0
c := class(i1, i2):
    (i1:)M<override>():int = 1
    (i2:)M<override>():int = 2
d := class(c):
    V:int = 7
both := class(i1, i2):
    M<override>():int = 3
Main():void =
    X := c{}
    A:i1 = X
    B:i2 = X
    Print("{A.M()} {B.M()}")
    Print("{X.(i1:)M()} {X.(i2:)M()}")
    Y := d{}
    As:[]i1 = array{X, Y, both{}}
    for (Z : As) { Print("{Z.M()}") }
    Bs:[]i2 = array{X, both{}}
    for (Z : Bs) { Print("{Z.M()} {Z.N()}") }
