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

Half(X:int)<decides>:int =
    X > 0
    Floor(X / 2)
Half(S:string):string = "half of {S}"

# nested overloaded calls resolve in polynomial time
Depth(X:int):int = X + 1
Depth(S:string):int = 0
Depth(C:char):int = 2

# arguments whose own type differs from their type at the parameter
Opt(O:?int):string = if (V := O?) then "some {V}" else "none"
Opt(X:int):string = "int {X}"
Pair(T:tuple(int, ?int)):string = "pair"
Pair(X:int):string = "int"

Main():void =
    Print(Describe(3))
    Print(Describe("hi"))
    Print(Describe(square{S := 4}))
    Print(Describe(circle{R := 2}))
    Print(Describe(color.Red))
    Print(Describe(2, 5))
    Print(Describe())
    Print(Describe(Describe(1)))
    if (H := Half[8]) then Print("{H}")
    Print(Half("x"))
    Print("{Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(1))))))))))))))))))))))))}")
    Print("{Opt(false)} {Opt(3)} {Pair((1, false))} {Pair(2)}")
