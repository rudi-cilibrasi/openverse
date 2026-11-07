# set P op= e reads P before e, in the direct and the path form alike (#58):
# set X += e is set X = X + e (Book of Verse)

counted := interface:
    var Count:int = 0
    Fixed:int = 0
named := interface:
    Name:string = "?"
a := class(counted, named):
    Extra:int = 1
b := class(named, counted):
    Other:int = 2
plain := class:
    var Count:int = 0
hold := class:
    var Item:counted
phold := class:
    var Item:plain
Mut(C:counted)<transacts>:int =
    Print("rhs")
    set C.Count = 100
    7
MutP(C:plain)<transacts>:int =
    set C.Count = 100
    7
Swap(H:hold)<transacts>:int =
    Print("swap")
    set H.Item = a{}
    3
Idx(I:int)<transacts>:int =
    Print("idx")
    I
Main():void =
    C:counted = b{}
    set C.Count = Mut(C)
    Print("direct= {C.Count}")
    set C.Count = 0
    set C.Count += Mut(C)
    Print("direct+= {C.Count}")
    P := plain{}
    set P.Count += MutP(P)
    Print("plain direct+= {P.Count}")
    H := hold{Item := b{}}
    set H.Item.Count += Mut(H.Item)
    Print("path+= {H.Item.Count}")
    PH := phold{Item := plain{}}
    set PH.Item.Count += MutP(PH.Item)
    Print("plain path+= {PH.Item.Count}")
    Old := H.Item
    set H.Item.Count = Swap(H)
    Print("swap: old {Old.Count} new {H.Item.Count}")
    Hs:[]hold = array{H}
    if (set Hs[Idx(0)].Item.Count = Mut(H.Item)) {}
    Print("arr {H.Item.Count}")
