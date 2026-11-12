Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
cell:=class{var R:rational=0}
Rhs(C:cell):rational=
    set C.R=100
    1
Main():void=
    if(A:=1/2):
        C:=cell{R:=A}
        set C.R+=Rhs(C)
        Check("saved",C.R,3,2)
        set C.R-=1
        set C.R*=2
        Check("one",C.R,1,1)
        if(set C.R/=0)then Print("bad")else Check("rollback",C.R,1,1)
        if(set C.R/=2)then Check("half",C.R,1,2)else Print("bad")
