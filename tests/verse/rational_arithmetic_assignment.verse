Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
cell:=class{var R:rational=0}
Rhs(C:cell):rational=
    set C.R=100
    1
Main():void=
    if(A:=1/2):
        C:=cell{R:=A}
        # (Rhs first, then the old value it left: 100 + 1)
        set C.R+=Rhs(C)
        Check("after rhs",C.R,101,1)
        set C.R-=1
        set C.R*=2
        Check("two hundred",C.R,200,1)
        if(set C.R/=0)then Print("bad")else Check("rollback",C.R,200,1)
        if(set C.R/=2)then Check("half",C.R,100,1)else Print("bad")
