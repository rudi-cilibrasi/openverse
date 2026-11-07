# expect: G calls F, which has the effect <writes>
box := class:
    var V:int = 0
F(X:int):int = X
F(B:box):int =
    set B.V = 1
    0
G(B:box)<computes>:int = F(B)
Main():void = Print("{G(box{})}")
