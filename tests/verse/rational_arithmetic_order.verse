Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
cell:=class{var N:int=0;var R:rational=0}
Left(C:cell):rational=
    set C.N+=1
    Print("left {C.N}")
    C.R
Right(C:cell):rational=
    set C.N+=1
    set C.R=100
    Print("right {C.N}")
    1
Main():void=
    if(A:=1/2):
        C:=cell{R:=A}
        Check("sum",Left(C)+Right(C),3,2)
        Check("neg",-Left(C),-100,1)
        Print("state {C.N} {Floor(C.R)}")
