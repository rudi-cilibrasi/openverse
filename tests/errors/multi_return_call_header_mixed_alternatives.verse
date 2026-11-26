# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#780, #686) As multi_return_call_header_failing_alternative, with an
# alternative of another type that has a value: the rows of `Many(S)` are
# of an int and the row of `2.5` is of a float, and the cursor that resumes
# the header has one row type. After a clause, and with a generic callee.
Cell := class{var N:int = 0}
Many(S:Cell, X:t where t:type)<transacts>:t =
    set S.N += 1
    X | X
Find(S:Cell)<transacts>:int =
    for (W := S.N, V := (Many(S, 3) | 2.5)):
        Y := 1 | 100
        if (Y = 100, S.N > 2):
            return Y
        Print("advance {Y} {W} {S.N}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
