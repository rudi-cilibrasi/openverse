cell:=class{var N:int=0}
Pick(C:cell,X:int)<computes>:int=X
Pick(C:cell,X:string)<reads><writes>:int=
    set C.N+=1
    Print("write {C.N}")
    42
Pure(C:cell)<computes>:int=Pick(C,7)
Main():void=
    C:=cell{}
    Print("pure {Pure(C)} {C.N}")
    if(Pick(C,"s"),false?)then Print("bad")else Print("rollback {C.N}")
    Print("live {Pick(C,"s")} {C.N}")
