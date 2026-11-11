cell:=class{var N:int=0}
Tick(C:cell,Tag:string):int=
    set C.N+=1
    Print("{Tag} {C.N}")
    C.N
Arg(C:cell,X:t where t:type):t=
    N:=Tick(C,"arg")
    X
box:=class:
    C:cell
    Later(X:u where u:type)<suspends>:u=
        N:=Tick(C,"begin")
        defer: Print("cleanup {C.N}")
        Sleep(1.0)
        Print("end {C.N}")
        X
Touch(B:box):box=
    N:=Tick(B.C,"receiver")
    B
Apply(F:type{_(:u)<suspends>:u},X:u where u:subtype(comparable))<suspends>:int=
    R:=F(X)
    if(R=X)then 1 else -1
Call(B:box,X:u where u:subtype(comparable))<suspends>:int=
    Apply(Touch(B).Later,Arg(B.C,X))
Run(B:box,X:t where t:subtype(comparable))<suspends>:void=
    T:=spawn{Call(B,X)}
    R:=T.Await()
    Print("done {R} {B.C.N}")
    race:
        Call(B,X)
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(box{C:=cell{}},"input")
