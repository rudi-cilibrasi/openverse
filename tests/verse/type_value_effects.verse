# A type value is made, and a cast through it runs, with no effect: a
# <computes> function may name a class as a value and cast through one
# (Book of Verse ch. 11, "Metatypes"; the API reference's <reads> functions
# return type values).
shape := class<abstract>:
    Area():int
square := class<concrete>(shape):
    Area<override>():int = 4
circle := class<concrete>(shape):
    Area<override>():int = 3
Kind(Round:logic)<computes>:subtype(shape) = if (Round?) then circle else square
Is(T:subtype(shape), S:shape)<computes>:string = if (T[S]) then "yes" else "no"
Main():void =
    Print("{Is(Kind(false), square{})} {Is(Kind(true), square{})} {Is(Kind(true), circle{})}")
