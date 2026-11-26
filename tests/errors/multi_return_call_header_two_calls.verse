# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#761, #686) One clause of a returning loop's header can call a function
# with several values where it is written, when the body has a choice that
# resumes the header (tests/verse/multi_return_call_header_resume). A second
# such clause is refused, as two conditionals with such calls are.
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Find(S:Cell)<transacts>:int =
    for (V := Many(S), W := Many(S)):
        Y := V | W + 100
        if (V = 6, W = 4):
            return Y
        Print("advance {V} {W} {Y}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
