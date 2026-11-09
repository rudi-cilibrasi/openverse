# expect: 3:4: base.Vals has several values, but another class or interface
base := class:
    Vals()<transacts>:int = 1 | 2
sub := class(base):
    Vals<override>()<transacts>:int = 3 | 4
Main()<transacts>:void =
    O : base = sub{}
    for (X := O.Vals()):
        Print("{X}")
