# an interface's field, at different places in its classes, read and written from generic code when classes fix the interface's type arguments (#157)
holder(t:type) := interface:
    var Item:t
    Label:string = "holder"
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
intbox := class(holder(int)):
    N:int = 0
strbox := class(holder(string)):
    S:string = "s"
Get(H:holder(t) where t:type):t = H.Item
Put(H:holder(t), V:t where t:type):void = set H.Item = V
Swap(A:holder(t), B:holder(t) where t:type):void =
    T := A.Item
    set A.Item = B.Item
    set B.Item = T
Main():void =
    I := intbox{Item := 1}
    S := strbox{Item := "a"}
    U := sub(int){Item := 2}
    Print("{Get(I)} {Get(S)} {Get(U)}")
    Put(I, 10)
    Put(S, "b")
    Put(U, 20)
    Print("{I.Item} {S.Item} {U.Item}")
    Swap(I, U)
    Print("{I.Item} {U.Item} {I.Label} {S.Label}")
    Hs:[]holder(int) = array{I, U, intbox{Item := 5}}
    for (H : Hs) { Print("{Get(H)}") }
