# expect: Find has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# (#780, #686) As multi_return_call_header_enclosed_flat, with the call
# inside `first{}` of the loop's own function. That function has one value
# in the elaboration that notes the header's cursor, so the header looks
# like a search there; the cursor's elaboration refuses it only where the
# cursor's owner is made, in the next one. It is noted as refused there
# too, and the analysis after it does not take the header.
Cell := class{var N:int = 0}
Find(S:Cell, D:int)<transacts>:int =
    if (D > 2):
        return 0
    for (F := first{Find(S, D + 1)}, V := (3 | 5)):
        Y := V | V + 100
        if (Y = 105, S.N > 2):
            return Y + F
        set S.N += 1
        Print("advance {D} {V} {Y} {S.N}")
    S.N
Main()<transacts>:void =
    for (X := Find(Cell{}, 0)):
        Print("{X}")
