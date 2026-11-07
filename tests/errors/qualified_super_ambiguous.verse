# expect: (super:)M is ambiguous here: c.(i1:)M and c.(i2:)M
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    (i1:)M<override>():int = 1
    (i2:)M<override>():int = 2
d := class(c):
    M<override>():int = 10 + (super:)M()
Main():void = Print("x")
