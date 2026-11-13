# A parameter of a function type written as a signature, `F(:t)<effects>:u`
# (Book of Verse ch. 6, "Examples"; its DefaultNamed tests), named or not,
# with named parameters of its own and a default (#503).
Map(Items:[]t, F(:t)<transacts>:u where t:type, u:type)<transacts>:[]u =
    for (Item:Items):
        F(Item)
Filter(Items:[]t, Pred(:t)<computes><decides>:void where t:type)<computes>:[]t =
    for (Item:Items, Pred[Item]):
        Item
Fold(Items:[]t, Initial:u, F(:u, :t)<transacts>:u where t:type, u:type)<transacts>:u =
    var Acc:u = Initial
    for (Item:Items):
        set Acc = F(Acc, Item)
    Acc
Values := array{1, 2, 3, 4, 5}
Square(X:int)<computes>:int = X * X
IsOdd(X:int)<computes><decides>:void = Mod[X, 2] = 1
AddTo(Acc:int, X:int)<computes>:int = Acc + X
HelloFunc():string = "Hello"
HiFunc():string = "Hi"
Greet(?Say():string = HelloFunc):string = Say()
Join1(F(?A:int):int):int = F(?A := 1)
Join2(F(?A:int = 0):int):int = F() + F(?A := 2)
F6(?A:int = 6):int = A
Main():void =
    M := Map(Values, Square)
    Fl := Filter(Values, IsOdd)
    Print("{M.Length} {Fl.Length} {Fold(Values, 0, AddTo)}")
    for (X : M) { Print("{X}") }
    Print("{Greet()} {Greet(?Say := HiFunc)}")
    Print("{Join1(F6)} {Join2(F6)}")
