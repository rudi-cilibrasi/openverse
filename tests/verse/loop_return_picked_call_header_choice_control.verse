# The control of loop_return_picked_call_header_choice: `left`'s method and
# the two functions have names of their own, and `Direct` and `Over` have
# their calls' values written as a choice. The output is the same.
left := class:
    Many()<transacts>:int = 4 | 1
single := class:
    Vals()<transacts>:int = 5
# The call a clause: the rows (4, 4) and (4, 5), which returns.
Direct(L:left)<transacts>:int =
    for (V := (4 | 1), U := (V | V + 1)):
        Y := U | U + 100
        if (U = 5):
            return Y
        Print("direct {V} {U} {Y}")
    0
# The call in a conditional's branch, the condition's call of one value.
Branch(S:single, L:left)<transacts>:int =
    for (V := if (S.Vals() = 5) then L.Many() else S.Vals(), U := (V | V + 1)):
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
# The rows (4, 4) and (4, 5), which returns.
Pair(B:int)<transacts>:int =
    B | B - 3
Sum(B:int, C:int)<transacts>:int =
    B + C
Over()<transacts>:int =
    for (V := (4 | 1), U := (V | V + 1)):
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
    Print("{Sum(1, 2)}")
