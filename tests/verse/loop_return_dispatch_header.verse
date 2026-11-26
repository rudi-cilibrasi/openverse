# (#764) A function with several values that returns from a `for` whose
# clauses call an overridden method with several values. The call is a
# dispatch on the receiver's class, an exclusive choice of the
# implementations whose guards bind the receiver for the one they pick. The
# loop's lowering names the function's locals apart before it moves the loop
# into a function of its own, and it named an alternative's guards apart
# from the value they are bound for: `unknown identifier '$d6_20'`.
#
# `derived`'s Vals gives 3 then 1, `base`'s 4 then 1. The loop returns in
# its first row, so Find gives that row's V, then V + 10. Each control has
# the same clauses and no return (its rows are an array), or the receiver
# whose class overrides nothing.
base := class:
    Vals()<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 1
# The issue's program: 3, 13; a `base` gives 4, 14.
Find(B:base)<transacts>:int =
    for (V := B.Vals()):
        return V | V + 10
    0
Rows(B:base)<transacts>:[]int =
    for (V := B.Vals()):
        V
# A return of one value, in the row that has V = 1: the rows before it fall
# through, and the values after the loop are not reached. 1.
InIf(B:base)<transacts>:int =
    for (V := B.Vals()):
        if (V = 1):
            return V
    7 | 8
# No row has V = 9, so the loop ends and the function's own values follow: 7, 8.
Miss(B:base)<transacts>:int =
    for (V := B.Vals()):
        if (V = 9):
            return V
    7 | 8
# Values that do not use the row: 5, 6.
Fixed(B:base)<transacts>:int =
    for (V := B.Vals()):
        return 5 | 6
    0
# The loop in a block: 5.
InBlock(B:base)<transacts>:int =
    block:
        for (V := B.Vals()):
            return 5
    7 | 8
# The call in an `if`'s conditions in the body of a `for` over a range.
# I = 1: V = 3 fails, V = 1 holds. 1, 11.
Body(B:base)<transacts>:int =
    for (I := 1..3):
        if (V := B.Vals(), V = I):
            return V | V + 10
    0
# The call as a `loop`'s returned value: 3, 1, 7.
Operand(B:base)<transacts>:int =
    loop:
        return B.Vals() | 7
# A `loop` with such a `for` in it, which does not return, and a return
# after it. First pass: N = 3 + 1 = 4, no value of Vals is over 4, 4 is not
# over 7. Second pass: N = 8, none is over 8, 8 is over 7. 8, 9. (The
# `break` is never taken: it gives the loop an end that is not a return.)
InLoop(B:base)<transacts>:int =
    var N:int = 0
    loop:
        for (V := B.Vals()):
            set N += V
        if (B.Vals() > N):
            return 5
        if (N > 7):
            return N | N + 1
        if (N > 100):
            break
    0
# An interface's method: `square` gives 3, 13 and `circle` 5, 15.
shape := interface:
    Sides()<transacts>:int
square := class(shape):
    Sides<override>()<transacts>:int = 3 | 1
circle := class(shape):
    Sides<override>()<transacts>:int = 5 | 6
FindSides(S:shape)<transacts>:int =
    for (V := S.Sides()):
        return V | V + 10
    0
SideRows(S:shape)<transacts>:[]int =
    for (V := S.Sides()):
        V
# A generic class's method: `swapped` gives Y then X.
pair(t:type) := class:
    X:t
    Y:t
    Both()<transacts>:t = X | Y
swapped(t:type) := class(pair(t)):
    Both<override>()<transacts>:t = Y | X
FindBoth(P:pair(int))<transacts>:int =
    for (V := P.Both()):
        return V | V + 10
    0
BothRows(P:pair(int))<transacts>:[]int =
    for (V := P.Both()):
        V
# An override with a result of its own class.
animal := class:
    Name:string = "animal"
    Kin()<transacts>:animal = animal{Name := "a1"} | animal{Name := "a2"}
dog := class(animal):
    Kin<override>()<transacts>:dog = dog{Name := "d1"} | dog{Name := "d2"}
FindKin(A:animal)<transacts>:string =
    for (V := A.Kin()):
        return V.Name | "more"
    "none"
KinRows(A:animal)<transacts>:[]string =
    for (V := A.Kin()):
        V.Name
# Overrides that call the one above them. A `leaf`'s Links gives 9, then
# `mid`'s: `link`'s 4 and 1, each with 100 added, then 2. The first over 100
# is 104: 104, 114. The method itself can hold the loop, its receiver Self.
link := class:
    Links()<transacts>:int = 4 | 1
    Seek()<transacts>:int =
        for (V := Links(), V > 100):
            return V | V + 10
        0
mid := class(link):
    Links<override>()<transacts>:int = (super:)Links() + 100 | 2
leaf := class(mid):
    Links<override>()<transacts>:int = 9 | (super:)Links()
FindLinks(L:link)<transacts>:int =
    for (V := L.Links(), V > 100):
        return V | V + 10
    0
LinkRows(L:link)<transacts>:[]int =
    for (V := L.Links(), V > 100):
        V
Main()<transacts>:void =
    for (X := Find(derived{})):
        Print("found {X}")
    for (X : Rows(derived{})):
        Print("row {X}")
    for (X := Find(base{})):
        Print("base found {X}")
    for (X : Rows(base{})):
        Print("base row {X}")
    for (X := InIf(derived{})):
        Print("in if {X}")
    for (X := Miss(derived{})):
        Print("miss {X}")
    for (X := Fixed(derived{})):
        Print("fixed {X}")
    for (X := InBlock(derived{})):
        Print("in block {X}")
    for (X := Body(derived{})):
        Print("body {X}")
    for (X := Operand(derived{})):
        Print("operand {X}")
    for (X := InLoop(derived{})):
        Print("in loop {X}")
    for (X := FindSides(square{})):
        Print("square {X}")
    for (X : SideRows(square{})):
        Print("square row {X}")
    for (X := FindSides(circle{})):
        Print("circle {X}")
    for (X : SideRows(circle{})):
        Print("circle row {X}")
    for (X := FindBoth(swapped(int){X := 1, Y := 2})):
        Print("swapped {X}")
    for (X : BothRows(swapped(int){X := 1, Y := 2})):
        Print("swapped row {X}")
    for (X := FindBoth(pair(int){X := 1, Y := 2})):
        Print("pair {X}")
    for (X : BothRows(pair(int){X := 1, Y := 2})):
        Print("pair row {X}")
    for (X := FindKin(dog{})):
        Print("dog {X}")
    for (X : KinRows(dog{})):
        Print("dog row {X}")
    for (X := FindKin(animal{})):
        Print("animal {X}")
    for (X := FindLinks(leaf{})):
        Print("leaf {X}")
    for (X : LinkRows(leaf{})):
        Print("leaf row {X}")
    for (X := FindLinks(link{})):
        Print("link {X}")
    for (X := leaf{}.Seek()):
        Print("leaf seek {X}")
