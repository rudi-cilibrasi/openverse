# regression test from the #67 review (p2)
shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R
Main():void =
    Sq := array{square{S := 1}}
    B := Sq + array{circle{R := 1}}
    Print("{B.Length}")
