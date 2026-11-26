# expect: this loop is left by a return of a function with several values, and its body or a returned value calls an overridden method with several values: not supported yet (#686, #764)
# The method's name is also an unrelated class's (`plain`). The receiver's
# class tells the family, `base`'s, which has an override: the call is a
# dispatch, refused in a returned value of a loop that goes on to another
# iteration, as it is when one family has the name
# (tests/errors/loop_return_dispatch_operand). The same call among a for's
# clauses is supported (tests/verse/loop_return_shared_method_override).
base := class:
    Vals()<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 1
plain := class:
    Vals()<transacts>:int = 6 | 5
Find(B:base)<transacts>:int =
    for (I := 1..3):
        if (I = 2):
            return B.Vals() | 7
    0
Main()<transacts>:void =
    for (X := Find(derived{})):
        Print("found {X}")
    for (X := plain{}.Vals()):
        Print("plain {X}")
