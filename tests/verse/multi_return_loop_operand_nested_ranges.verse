Choose(OuterLimit:int,InnerLimit:int)<transacts>:int=
    var Count:int=0
    for(I:=1..OuterLimit):
        defer:
            Print("outer cleanup {I} ({Count})")
        for(J:=1..InnerLimit):
            set Count+=1
            defer:
                Print("inner cleanup {I} {J} ({Count})")
            if(I=2,J=2):
                return Count|block{Print("second operand");Count+1}
    Count+100|Count+101

Main()<transacts>:void=
    for(V:=Choose(2,2)){Print("all {V}")}
    if(V:=Choose(2,2), V=4)then Print("first {V}")else Print("bad first")
    if(V:=Choose(2,2), V=99)then Print("bad reject")else Print("none")
    for(V:=Choose(1,1)){Print("suffix {V}")}
