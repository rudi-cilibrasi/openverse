# (#686) A returning loop, in a function with several values, whose header
# has a written choice and a call that only an elaboration tells the values
# of: of a method whose name unrelated classes share (the receiver's class
# picks it), or of an overloaded function (the arguments' types do). The
# first analysis notes the header's cursor with the call as written, of one
# value; once the call is found to have several, its values are rows and the
# cursor is another, noted again. (Before, the first one's type was used for
# it: `Branch` was refused with a mismatch of two cursor tuples, and
# `Direct` and `Over` with the general message.)
# The same loops over methods and functions with names of their own are
# loop_return_picked_call_header_choice_control.
left := class:
    Vals()<transacts>:int = 4 | 1
single := class:
    Vals()<transacts>:int = 5
# The call a clause: the rows (4, 4) and (4, 5), which returns.
Direct(L:left)<transacts>:int =
    for (V := L.Vals(), U := (V | V + 1)):
        Y := U | U + 100
        if (U = 5):
            return Y
        Print("direct {V} {U} {Y}")
    0
# The call in a conditional's branch, the condition's call of one value.
Branch(S:single, L:left)<transacts>:int =
    for (V := if (S.Vals() = 5) then L.Vals() else S.Vals(), U := (V | V + 1)):
        Y := U | U + 100
        if (U = 5):
            return Y
        Print("branch {V} {U} {Y}")
    0
# The call of one value: the rows (5, 5) and (5, 6), as before.
One(S:single)<transacts>:int =
    for (V := S.Vals(), U := (V | V + 1)):
        Y := U | U + 100
        if (U = 6):
            return Y
        Print("one {V} {U} {Y}")
    0
# An overloaded function, the overload of one argument: the rows (4, 4)
# and (4, 5), which returns.
Pair(B:int)<transacts>:int =
    B | B - 3
Pair(B:int, C:int)<transacts>:int =
    B + C
Over()<transacts>:int =
    for (V := Pair(4), U := (V | V + 1)):
        Y := U | U + 100
        if (U = 5):
            return Y
        Print("over {V} {U} {Y}")
    0
Main()<transacts>:void =
    for (X := Direct(left{})):
        Print("d {X}")
    for (X := Branch(single{}, left{})):
        Print("b {X}")
    for (X := One(single{})):
        Print("o {X}")
    for (X := Over()):
        Print("v {X}")
    Print("{Pair(1, 2)}")
