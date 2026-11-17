counter:=class<concrete>:
    var Count:int=0
Low(C:counter)<transacts>:int=
    set C.Count+=1
    1
High(C:counter,OK:logic)<transacts><decides>:int=
    set C.Count+=10
    OK?
    2

Choose(C:counter,OK:logic)<transacts>:int=
    for(I:=1..2):
        for(J:=Low(C)..High[C,OK]):
            if(I=2,J=2):
                return C.Count|C.Count+1
    C.Count+100|C.Count+101

Main()<transacts>:void=
    C:=counter{}
    for(V:=Choose(C,false)){Print("failed endpoint {V} {C.Count}")}
    D:=counter{}
    for(V:=Choose(D,true)){Print("successful endpoint {V} {D.Count}")}
    E:=counter{}
    if(V:=Choose(E,true),V=23)then Print("second {V} {E.Count}")else Print("bad second")
    F:=counter{}
    if(V:=Choose(F,true),V=99)then Print("bad reject")else Print("rejected {F.Count}")
