# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#761, #686) The call in the header of a returning loop whose body has a
# choice is of an overloaded function. Which overload it takes is picked by
# an elaboration, and until then the call is as written, of one value: the
# header has no choice then and the loop is refused, as it is with the call
# in a conditional's branches. With names of their own the overloads are
# supported (tests/verse/multi_return_call_header_resume).
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Many(S:Cell, B:int)<transacts>:int =
    set S.N += 1
    B | B + 2
Find(S:Cell)<transacts>:int =
    for (V := Many(S, 4)):
        Y := V | V + 100
        if (V = 6):
            return Y
        Print("advance {V} {Y}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
    for (X := Many(Cell{})):
        Print("{X}")
