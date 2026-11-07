# a qualified call on a receiver of a type with no instance (#98, review)
i2 := interface:
    M5(P6:int)<computes>:int = P6
i8 := interface(i2):
    M11():int = (i2:)M5(1)
c := class(i2):
    U:int = 0
Main():void =
    Print("x")
