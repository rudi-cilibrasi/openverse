# overloading (#74, Book of Verse ch. 6): functions of one name taking
# disjoint parameter types; a call takes the one its arguments fit

shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class:
    R:int
color := enum:
    Red
    Green

Describe(X:int):string = "int {X}"
Describe(S:string):string = "string {S}"
Describe(B:shape):string = "shape {B.Area()}"
Describe(C:circle):string = "circle {C.R}"
Describe(K:color):string = "color"
Describe(X:int, Y:int):string = "two {X + Y}"
Describe():string = "nothing"
Describe(O:?int):string = if (V := O?) then "some {V}" else "none"

Half(X:int)<decides>:int =
    X > 0
    Floor(X / 2)
Half(S:string):string = "half of {S}"

Main():void =
    Print(Describe(3))
    Print(Describe("hi"))
    Print(Describe(square{S := 4}))
    Print(Describe(circle{R := 2}))
    Print(Describe(color.Red))
    Print(Describe(2, 5))
    Print(Describe())
    Print(Describe(option{7}))
    Print(Describe(Describe(1)))
    if (H := Half[8]) then Print("{H}")
    Print(Half("x"))
