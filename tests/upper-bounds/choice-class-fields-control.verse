vehicle:=class<allocates>:
    var N:int=1
car:=class<allocates>(vehicle){Name:string="left"}
ca:=class:
    var Item:car
    K:int=0
cb:=class:
    var Item:car
    K:string="other"
Dup(X:t where t:type)<computes>:t=X|X
Run(X:car,Y:car)<suspends>:car=
    defer:Print("cleanup {Y.N}")
    P:=ca{Item:=X}
    Q:=cb{Item:=X}
    for(A:=(Dup(P)|Dup(Q))):
        set A.Item=Y
        Sleep(0.1)
        set A.Item.N+=1
        Print("item {A.Item.N}")
    Print("aliases {X.N} {Y.N}")
    Y
Main()<suspends>:void=
    A:=car{}
    B:=car{Name:="right"}
    R:=Run(A,B)
    Print("precise {R.Name} {R.N}")
    C:=car{}
    D:=car{Name:="cancel"}
    race:
        Run(C,D)
        block:
            Sleep(0.25)
            Print("winner")
    Print("cancel {D.Name} {D.N} {C.N}")
