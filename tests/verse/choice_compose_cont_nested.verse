# A composed choice nested in an alternative of another, with another such
# choice after (#338): its continuation is keyed by the places of the
# clauses after it too, as in the next elaboration it has the outer
# continuation's call after it, which may use the same names
RT2(X:int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
RT3(X:int)<transacts>:int =
    if (X > 100):
        return 1
    X * 10 | X * 20
Main()<transacts>:void =
    if (V := first{Y := (RT3(RT2(2)) | 4) + RT2(-1); Y > 25; Y}) then Print("first {V}") else Print("none")
    S := option{"<{((RT3(RT2(2)) | 4) + RT2(-1))}>"}
    if (T := S?) then Print(T) else Print("no")
