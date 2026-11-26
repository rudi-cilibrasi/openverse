# expect: this loop is left by a return of a function with several values, and its body or a returned value calls an overridden method with several values: not supported yet (#686, #764)
# A `for` over a range or a collection that returns several values steps in
# a function of its own, which calls itself for the next element, and a
# dispatch there is no call that function takes lazily. The refusal is said
# of the loop the program wrote, not of that function. The same call among
# a for's clauses or an if's conditions is supported
# (tests/verse/loop_return_dispatch_header).
base := class:
    Vals()<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 1
Find(B:base)<transacts>:int =
    for (I := 1..3):
        if (I = 2):
            return B.Vals() | 7
    0
Main()<transacts>:void =
    for (X := Find(derived{})):
        Print("found {X}")
