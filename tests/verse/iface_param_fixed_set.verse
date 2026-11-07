# regression test from the #53 review (p67)
holder(t:type) := interface:
    var Item:t
box(t:type) := class(holder(t)):
    N:int = 0
intbox := class(holder(int)):
    M:int = 0
Put(H:holder(t), X:t where t:type):void = set H.Item = X
Main():void =
    B := intbox{Item := 1}
    Put(B, 9)
    Print("{B.Item}")
