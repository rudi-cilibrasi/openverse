# (#686, #764) A loop return of several values from a `for` over a call of a
# method whose name two unrelated families declare, one of which overrides
# it. The receiver's class tells the family: in `base`'s the call is a
# dispatch, which picks the implementation of the receiver's own class, a
# class declared after the function too; in `plain`'s, which has one
# implementation, it is that one's call. An interface declares the name as
# well, a third family, whose calls dispatch.
#
# `base`'s Vals gives 4 then 1, `derived`'s 3 then 1, `late`'s 9 then 2;
# `plain`'s 6 then 5; `square`'s 30 then 31 and `circle`'s 50 then 51.
base := class:
    Vals()<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 1
plain := class:
    Vals()<transacts>:int = 6 | 5
shape := interface:
    Vals()<transacts>:int
square := class(shape):
    Vals<override>()<transacts>:int = 30 | 31
circle := class(shape):
    Vals<override>()<transacts>:int = 50 | 51
Find(B:base)<transacts>:int =
    for (V := B.Vals()):
        return V | V + 10
    0
Rows(B:base)<transacts>:[]int =
    for (V := B.Vals()):
        V
FindPlain(P:plain)<transacts>:int =
    for (V := P.Vals()):
        return V | V + 10
    0
PlainRows(P:plain)<transacts>:[]int =
    for (V := P.Vals()):
        V
FindShape(S:shape)<transacts>:int =
    for (V := S.Vals()):
        return V | V + 10
    0
ShapeRows(S:shape)<transacts>:[]int =
    for (V := S.Vals()):
        V
# The receiver's static class is `derived`, and `late` below it overrides
# the method again: the call still dispatches.
FindDerived(D:derived)<transacts>:int =
    for (V := D.Vals(), V > 1):
        return V | V + 10
    0
# Both families in one header: the first row with V + W = 8 is (3, 5) for a
# `derived`: 35, 53. For a `base`, no row: 0.
FindPair(B:base, P:plain)<transacts>:int =
    for (V := B.Vals(), W := P.Vals(), V + W = 8):
        return V * 10 + W | W * 10 + V
    0
# A receiver of a type parameter below `base`: a dispatch too.
FindBelow(B:t where t:subtype(base))<transacts>:int =
    for (V := B.Vals()):
        return V | V + 10
    0
late := class(derived):
    Vals<override>()<transacts>:int = 9 | 2
Main()<transacts>:void =
    for (X := Find(base{})):
        Print("base {X}")
    for (X : Rows(base{})):
        Print("base row {X}")
    for (X := Find(derived{})):
        Print("derived {X}")
    for (X : Rows(derived{})):
        Print("derived row {X}")
    for (X := Find(late{})):
        Print("late {X}")
    for (X : Rows(late{})):
        Print("late row {X}")
    for (X := FindPlain(plain{})):
        Print("plain {X}")
    for (X : PlainRows(plain{})):
        Print("plain row {X}")
    for (X := FindShape(square{})):
        Print("square {X}")
    for (X : ShapeRows(square{})):
        Print("square row {X}")
    for (X := FindShape(circle{})):
        Print("circle {X}")
    for (X := FindDerived(derived{})):
        Print("as derived {X}")
    for (X := FindDerived(late{})):
        Print("as derived late {X}")
    for (X := FindPair(derived{}, plain{})):
        Print("pair {X}")
    for (X := FindPair(base{}, plain{})):
        Print("pair base {X}")
    for (X := FindBelow(base{})):
        Print("below base {X}")
    for (X := FindBelow(derived{})):
        Print("below derived {X}")
    for (X := FindBelow(late{})):
        Print("below late {X}")
