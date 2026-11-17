Long(N:int)<transacts>:int=
    var I:int=0
    loop:
        set I+=1
        if (I=N):
            return I|I+1
        if (I>N):
            break
    0

Main()<transacts>:void=
    for (V:=Long(20000)):
        Print("{V}")
