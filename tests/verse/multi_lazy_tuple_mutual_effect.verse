counter := class { var Log:string="" }
Note(C:counter,S:string,V:t where t:type)<transacts>:t =
    set C.Log = "{C.Log}{S}"
    V
Left(C:counter,A:int,B:int,N:int)<transacts><decides>:int =
    Note(C,"p",0)
    if(N>0) then (A | Right[(C,Note(C,"a",B),Note(C,"b",A),N-1)]) else A
Right(C:counter,X:int,Y:int,N:int)<transacts><decides>:int =
    Note(C,"q",0)
    if(N>0) then (X | Left[C,Y,X,N-1]) else X
Main()<transacts>:void =
    C:=counter{}
    if(V:=Left[C,3,4,2],V=4) then Print("int {V} {C.Log}")
    set C.Log=""
    if(V:=Left[C,3,4,2],V=99) then Print("bad") else Print("none {C.Log}")
