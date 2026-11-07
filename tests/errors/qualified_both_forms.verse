# expect: c implements M both plainly and as (i1:)M: give one or the other
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    M<override>():int = 2
    (i1:)M<override>():int = 1
Main():void = Print("x")
