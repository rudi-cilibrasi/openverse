# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#780, #686) The header of a returning loop whose body has a choice is a
# choice of a call of a function with several values and `false?`. The
# alternatives are stepped apart, each with a row of its own type (int, and
# logic for `false?`), and the cursor that resumes the header needs one row
# type: its elaboration says so when the header's cursor is noted, and the
# header is not taken (before, an internal error). With the values written,
# `for (V := (3 | 4 | 6 | false?))`, `V` is comparable and the loop is
# supported.
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Find(S:Cell)<transacts>:int =
    for (V := (Many(S) | false?)):
        Y := 1 | 100
        if (Y = 100, S.N > 2):
            return Y
        Print("advance {Y} {S.N}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
