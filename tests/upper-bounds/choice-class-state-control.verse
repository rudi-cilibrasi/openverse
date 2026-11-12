vehicle:=class<allocates>:
    var N:int=1
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string="a"}
Read(X:car,?V:int=X.N)<reads>:int=V
ca:=class:
    var K:int=0
    Apply(X:car,?V:int=Read(X))<transacts>:int=
        set K=V
        V
cb:=class:
    var K:rational=0
    Apply(X:car,?V:int=Read(X))<transacts>:int=
        set K=V
        V
Dup(X:t where t:type)<computes>:t=X|X
Run(X:car)<suspends>:car=
    defer:Print("cleanup {X.N}")
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        A.Apply(X)
        Sleep(0.1)
        set X.N+=1
        Print("row {X.N}")
        0
    Print("rows {Rows.Length}")
    if(Q.K=4)then Print("columns {P.K} 4")else Print("bad columns")
    X
Main()<suspends>:void=
    A:=car{}
    R:=Run(A)
    Print("precise {R.Name} {A.N}")
    B:=car{Name:="b"}
    race:
        Run(B)
        block:
            Sleep(0.25)
            Print("winner")
    Print("cancel {B.Name} {B.N}")
