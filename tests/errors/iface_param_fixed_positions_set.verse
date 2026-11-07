# expect: setting it is not supported yet
holder(t:type) := interface:
    var Item:t
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
intbox := class(holder(int)):
    N:int = 0
Put(H:holder(t), V:t where t:type):void = set H.Item = V
Main():void =
    I := intbox{Item := 1}
    Put(I, 2)
    Print("{I.Item}")
