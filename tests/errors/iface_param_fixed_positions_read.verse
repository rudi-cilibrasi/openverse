# expect: reading it is not supported yet
holder(t:type) := interface:
    var Item:t
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
intbox := class(holder(int)):
    N:int = 0
Get(H:holder(t) where t:type):t = H.Item
Main():void =
    Print("{Get(intbox{Item := 1}) + Get(sub(int){Item := 2})}")
