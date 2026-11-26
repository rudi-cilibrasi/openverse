# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#761, #686) A returning loop whose header calls a function with several
# values and whose body has a choice, inside another loop: refused, as it
# is with a written choice in the header.
Cell := class{var N:int = 0}
Many(S:Cell, B:int)<transacts>:int =
    set S.N += 1
    B | B + 2
Find(S:Cell)<transacts>:int =
    for (I := 0..1):
        for (V := Many(S, I)):
            Y := V | V + 100
            if (Y = 103):
                return Y
            Print("advance {I} {V} {Y}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
