# regression test from the #67 review (n3)
shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R
Main():void =
    C := 1
    A := if (C > 5) then array{Err()} else array{1}
    Print("{A.Length}")
