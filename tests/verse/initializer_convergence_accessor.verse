# A field default that reads or sets a field through an accessor (#157, #511):
# `Value` sits at different places in c1 and c2, so a read through holder(int)
# calls each class's accessor. Its convergence is checked through the accessor,
# not through the function at the accessor's place counted from 0 (First, an
# ordinary function, which a default may not call).
First()<transacts>:int = 7

holder(t:type) := interface:
    var Value:t

base := class:
    Pad:int = 0

c1 := class(holder(int)):
    var Value<override>:int = 1

c2 := class(base, holder(int)):
    var Value<override>:int = 2

shows := interface:
    S:int = block:
        H:holder(int) = c2{}
        H.Value

plain := class(shows):
    Y:int = block:
        H:holder(int) = c1{}
        H.Value

boxed(t:type) := class:
    W:?t = false
    Y:int = block:
        H:holder(int) = c2{}
        H.Value + 1

sub := class(plain):
    Y<override>:int = block:
        H:holder(int) = c2{}
        H.Value + 10

counter := class:
    var N:int = block:
        H:holder(int) = c1{}
        H.Value

setter := class:
    Y:int = block:
        H:holder(int) = c2{}
        set H.Value = 5
        H.Value

Main()<transacts>:void =
    P := plain{}
    Print("plain {P.Y} {P.S}")
    Print("boxed {boxed(string){}.Y}")
    Print("sub {sub{}.Y}")
    C := counter{}
    set C.N += 5
    Print("counter {C.N}")
    Print("setter {setter{}.Y} {First()}")
