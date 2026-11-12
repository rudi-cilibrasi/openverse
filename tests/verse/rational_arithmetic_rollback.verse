Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
cell:=class{var N:int=0;var R:rational=0}
Arg(C:cell,X:int)<transacts>:rational=
    set C.N+=1
    Print("arg {X} {C.N}")
    X
Main():void=
    C:=cell{}
    if(R:=Arg(C,1)/Arg(C,0))then Print("bad")else Print("miss {C.N}")
    if(R:=Arg(C,3)/Arg(C,2),set C.R=R,false?)then Print("bad")else Print("reject {C.N} {Floor(C.R)}")
    if(R:=Arg(C,3)/Arg(C,2))then Check("hit",R,3,2)else Print("bad")
    Print("state {C.N}")
