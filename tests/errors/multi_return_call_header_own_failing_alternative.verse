# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#780, #686) As multi_return_call_header_failing_alternative, with a call
# of the loop's own function beside `false?`: the rows' types differ, which
# the cursor's elaboration finds where the cursor's owner is made
# (multi_return_call_header_own_enclosed).
Cell := class{var N:int = 0}
Find(S:Cell, D:int)<transacts>:int =
    if (D > 2):
        return 0
    for (V := (Find(S, D + 1) | false?)):
        Y := 1 | 100
        if (Y = 100, S.N > 2):
            return Y
        set S.N += 1
        Print("advance {D} {Y} {S.N}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{}, 0)):
        Print("{X}")
