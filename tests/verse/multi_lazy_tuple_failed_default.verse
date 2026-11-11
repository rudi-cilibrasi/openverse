counter := class { var Log:string="" }
Note(C:counter,S:string,V:int)<transacts>:int =
    set C.Log = "{C.Log}{S}"
    V
Default(C:counter,N:int)<transacts><decides>:int =
    Note(C,"d",0)
    N>0
    1
Walk(C:counter,N:int,?Step:int=Default[C,N])<transacts><decides>:int =
    Note(C,"p",0)
    if(N>0) then (N | Walk[(C,N-Step)] | 99) else N
Main()<transacts>:void =
    C:=counter{}
    if(V:=Walk[C,1],V=99) then Print("win {V} {C.Log}")
    set C.Log=""
    if(V:=Walk[C,1],V=100) then Print("bad") else Print("none {C.Log}")
