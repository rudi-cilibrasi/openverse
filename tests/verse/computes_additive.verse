# <computes> with the additive heap specifiers (Book of Verse ch. 13: "A
# function may have at most one exclusive specifier but can combine multiple
# additive ones"; Attributes/allocates.versetest 6-32, unique.versetest
# 87-137): a construction or a call allows the effects of those.
counter := class<computes><allocates>:
    var N:int = 0
token := class<computes><allocates><unique> {}
shape := interface<computes><allocates>:
    Sides:int = 0
square := class<computes><allocates>(shape):
    Sides<override>:int = 4
point := struct<computes><allocates>:
    X:int = 0
Make(Start:int)<computes><allocates>:counter = counter{N := Start}
Read(C:counter)<computes><reads>:int = C.N
Bump(C:counter)<computes><reads><writes>:void = set C.N += 1
Main():void =
    C := Make(41)
    Bump(C)
    A := token{}
    B := token{}
    Print("{Read(C)} {if (A = B) then "same" else "different"} {square{}.Sides} {point{X := 2}.X}")
