probe:=class:
    var Reads:int=0
    var Stored:int=0
    var Gate<getter(GetGate)><setter(SetGate)>:int=external{}
    GetGate(:accessor)<transacts>:int=
        set Reads+=1
        Print("gate {Reads} {Stored}")
        Stored
    SetGate(:accessor,V:int)<transacts>:void=set Stored=V
F(H:probe)<transacts>:int=
    Y:=if(H.Gate<3)then(1|2)else(return 0)
    defer:set H.Stored+=1
    Y|Y+10
Main()<transacts>:void=
    A:=probe{}
    for(V:=F(A)){Print("all {V} {A.Stored}")}
    Print("all state {A.Reads} {A.Stored}")
    B:=probe{}
    if(V:=F(B),V=12)then Print("first {V}")else Print("bad")
    Print("first state {B.Reads} {B.Stored}")
    C:=probe{}
    if(V:=F(C),V=99)then Print("bad")else Print("none")
    Print("none state {C.Reads} {C.Stored}")
    E:=probe{Stored:=3}
    for(V:=F(E)){Print("early {V}")}
    Print("early state {E.Reads} {E.Stored}")
