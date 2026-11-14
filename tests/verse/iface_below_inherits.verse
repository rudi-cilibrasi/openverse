# An interface below another inherits its members and may add its own, but
# overrides none: a class below both sees the defaults of the interface that
# declares each member, and may override any (the Book's tests,
# Interface.versetest, InterfaceWithFields.versetest, InterfaceDiamond.versetest)
base_i := interface:
    Tag():string = "base"
    var Count:int = 1
sub_i := interface(base_i):
    Extra():string = "extra {Tag()}"
plain := class(base_i, sub_i) {}
own := class(sub_i):
    Tag<override>():string = "own"
    var Count<override>:int = 5
Main():void =
    P := plain{}
    Print("{P.Tag()} {P.Extra()} {P.Count}")
    O := own{}
    Print("{O.Tag()} {O.Extra()} {O.Count}")
    S:sub_i = O
    B:base_i = P
    Print("{S.Tag()} {B.Tag()}")
