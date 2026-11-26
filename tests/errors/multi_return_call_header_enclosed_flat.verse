# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#780, #686) A call of a function with several values inside `first{}`
# stays where its clause is compiled, in a failure context of its own, so
# the header is not a search that a returning loop's cursor can step. With
# a flat written choice in another clause the header was taken all the same
# and its cursor's elaboration stopped with an internal error; now that
# elaboration's verdict is noted and the header is not taken, as in
# multi_return_call_header_enclosed, where the choice is not flat.
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Find(S:Cell)<transacts>:int =
    for (F := first{Many(S)}, Q := (3 | 5), V := F + Q):
        Y := V | V + 100
        if (V = 8):
            return Y
        Print("advance {V} {Y}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
