counter := class { var Log:string="" }
Note(C:counter,S:string,V:int)<transacts>:int =
    set C.Log = "{C.Log}{S}"
    V
Walk(C:counter,A:int,B:int,N:int)<transacts><decides>:int =
    Note(C,"p",0)
    if(N>0) then (A | Walk[(C,Note(C,"a",B),Note(C,"b",A),N-1)]) else A
Run(Unused:t where t:type)<transacts>:void =
    C:=counter{}
    var Total:int=0
    if(V:=Walk[C,3,4,2],set Total+=V,E:[]t=Concatenate(),V=4) then Print("win {V} {Total} {E.Length} {C.Log}")
    set C.Log=""
    if(V:=Walk[C,3,4,2],set Total+=V,E:[]t=Concatenate(),V=99) then Print("bad") else Print("none {Total} {C.Log}")
Main()<transacts>:void =
    Run(7)
    Run("s")
