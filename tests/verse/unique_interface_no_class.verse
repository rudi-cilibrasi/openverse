# A <unique> interface or class that no concrete class is below is
# comparable, as one with instances is (#724): its values are compared by
# identity, and it has none (the Book's tests, ComparableInterface.versetest
# 5, 13, 26, 37; Epic's compiler and Verse VM, UEFN 43.12,
# followup-refused/unique-interface-equality: compiled). It is a map's key
# type too.
shape := interface<unique>:
    Sides():int
child := interface(shape):
    More():int
box(t:type) := interface<unique>:
    Get():t
lone := class<unique><abstract>{}

Same(A:shape, B:shape):logic = if (A = B) then true else false
Differ(A:child, B:child):logic = if (A <> B) then true else false
SameBox(A:box(int), B:box(int)):logic = if (A = B) then true else false
SameLone(A:lone, B:lone):logic = if (A = B) then true else false
Count(M:[shape]int):int = M.Length

Main():void =
    M:[shape]int = map{}
    Print("compiled {Count(M)}")
