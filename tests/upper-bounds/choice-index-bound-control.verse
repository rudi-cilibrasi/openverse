vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="a"}
ca:=class{var Items:[]int=array{0,0}}
cb:=class{var Items:[]rational=array{0,0}}
Read(X:car,?V:int=X.N)<reads>:int=V
Key(X:car)<transacts>:int=
    Print("key {X.N}")
    set X.N+=1
    0
BadKey(X:car)<transacts>:int=
    Print("bad key")
    set X.N+=100
    10
IntStep(X:car,P:ca)<suspends>:void=
    if(set P.Items[Key(X)]=Read(X)):
        Sleep(0.1)
        set X.N+=1
        Print("row {X.N}")
RatStep(X:car,Q:cb)<suspends>:void=
    if(set Q.Items[Key(X)]=Read(X)):
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
    if(V:=P.Items[0],W:=Q.Items[0],W=8):Print("columns {V} 8")
    if(set P.Items[BadKey(X)]=Read(X))then Print("bad")else Print("rolled index")
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
