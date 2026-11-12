vehicle:=class<allocates>:
    var N:int=1
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string="a"}
ca:=class{var K:int=0}
cb:=class{var K:rational=0}
Dup(X:t where t:type)<computes>:t=X|X
Read(X:t,?V:int=X.N,?F:type{_()<reads>:int}=X.ReadN where t:subtype(vehicle))<reads>:int=
    if(F()=V)then V else -1
Run(X:t where t:subtype(vehicle))<suspends>:t=
    defer:Print("cleanup {X.N}")
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        set A.K=Read(X)
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
