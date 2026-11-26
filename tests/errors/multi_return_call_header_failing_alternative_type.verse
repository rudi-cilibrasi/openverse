# expect: no operator '+' for comparable and int
# (#780) `V` of `for (V := (Many(S) | false?))` is of the alternatives'
# join, comparable, as it is with the values written (`(3 | false?)`): a
# body that adds to it is refused for that, where the function is checked
# as written (before, an internal error came first).
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Find(S:Cell)<transacts>:int =
    for (V := (Many(S) | false?)):
        Y := V | V + 100
        if (S.N > 2):
            return 7
        Print("advance {S.N}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{})):
        Print("{X}")
