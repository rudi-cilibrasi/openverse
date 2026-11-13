vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="a"}
ca:=class{var Items:[]int=array{0,0}}
cb:=class{var Items:[]rational=array{0,0}}
Dup(X:t where t:type)<computes>:t=X|X
Read(X:t,?V:int=X.N where t:subtype(vehicle))<reads>:int=V
Key(X:t where t:subtype(vehicle))<transacts>:int=
    Print("key {X.N}")
    set X.N+=1
    0
BadKey(X:t where t:subtype(vehicle))<transacts>:int=
    Print("bad key")
    set X.N+=100
    10
Run(X:t where t:subtype(vehicle))<suspends>:t=
    defer:Print("cleanup {X.N}")
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        if(set A.Items[Key(X)]=Read(X)):
            Sleep(0.1)
            set X.N+=1
            Print("row {X.N}")
            0
    Print("rows {Rows.Length}")
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
