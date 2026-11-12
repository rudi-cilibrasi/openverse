cell:=class{var N:int=0}
Tick(C:cell,Tag:string):int=
    set C.N+=1
    Print("{Tag} {C.N}")
    C.N
Pick(C:cell,X:int,?A:int,?B:int,?D:int=Tick(C,"default-D"),?E:int=Tick(C,"default-E")):int=
    Print("body {X} {A} {B} {D} {E}")
    X+A+B+D+E
Pick(C:cell,X:string,?A:string,?B:string,?D:int=Tick(C,"string-D"),?E:int=Tick(C,"string-E")):string=X+A+B
Main():void=
    C:=cell{}
    R:=Pick(C,Tick(C,"pos"),?B:=Tick(C,"B"),?A:=Tick(C,"A"))
    Print("result {R} {C.N}")
