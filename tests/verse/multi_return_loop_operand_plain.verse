Choose(Stop:int)<transacts>:int=
    var I:int=0
    loop:
        set I+=1
        defer:
            Print("cleanup {I}")
        loop:
            Print("inner {I}")
            break
        if (I=Stop):
            break
        if (I=2):
            return I|block{Print("second operand {I}");I+1}
    I+7|I+8

Main()<transacts>:void=
    for (V:=Choose(1)):
        Print("break yielded {V}")
    for (V:=Choose(3)):
        Print("return yielded {V}")
    if (V:=Choose(3), V=2):
        Print("first yielded {V}")
    if (V:=Choose(3), V=99):
        Print("unexpected {V}")
    else:
        Print("all rejected")
