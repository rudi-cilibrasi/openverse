counter := class { var Log:string="" }
Note(C:counter,S:string,V:int)<transacts>:int =
    set C.Log = "{C.Log}{S}"
    V
Next(C:counter,A:int,B:int,N:int)<transacts>:tuple(counter,int,int,int) =
    Note(C,"t",0)
    (C,A,B,N)
Walk(C:counter,A:int,B:int,N:int)<transacts><decides>:int =
    Note(C,"p",0)
    if(N>0) then (A | Walk[Next(C,B,A,N-1)]) else A
Unpack(P:tuple(counter,int,int,int))<transacts><decides>:int = Walk[P(0),P(1),P(2),P(3)]
Main()<transacts>:void =
    C:=counter{}
    if(V:=Walk[C,3,4,2],V=4) then Print("win {V} {C.Log}")
