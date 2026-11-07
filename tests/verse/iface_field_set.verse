# set of an interface field that sits at different places in the classes
# implementing the interface: a test of the object's class, as a read does

counted := interface:
    var Count:int = 0
named := interface:
    Name:string = "?"
# the fields sit at different places: a gives Count first, b Name first
a := class(counted, named):
    Extra:int = 1
b := class(named, counted):
    Other:int = 2
Bump(C:counted):void =
    set C.Count += 1
Holder := class:
    var Item:counted
Main():void =
    X := a{}
    Y := b{}
    Bump(X)
    Bump(Y)
    Bump(Y)
    Cs:[]counted = array{X, Y}
    for (C : Cs) { Print("{C.Count}") }
    for (C : Cs) { set C.Count = C.Count * 10 }
    for (C : Cs) { Print("{C.Count}") }
    H := Holder{Item := Y}
    set H.Item.Count = 99
    Print("{Y.Count}")
