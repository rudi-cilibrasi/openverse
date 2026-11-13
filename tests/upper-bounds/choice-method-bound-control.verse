vehicle:=class<allocates>{var N:int=1}
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
IntStep(X:car,P:ca)<suspends>:void=
    P.Apply(X)
    Sleep(0.1)
    set X.N+=1
    Print("row {X.N}")
RatStep(X:car,Q:cb)<suspends>:void=
    Q.Apply(X)
    Sleep(0.1)
    set X.N+=1
    Print("row {X.N}")
Run(X:car)<suspends>:car=
    defer:Print("cleanup {X.N}")
    P:=ca{}
    Q:=cb{}
    IntStep(X,P)
    IntStep(X,P)
    RatStep(X,Q)
    RatStep(X,Q)
    Print("rows 4")
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
