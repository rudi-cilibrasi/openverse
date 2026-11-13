vehicle:=class<allocates>:
    var N:int=1
car:=class<allocates>(vehicle){Name:string="left"}
ca(a:subtype(vehicle)):=class:
    var Item:a
    K:int=0
cb(a:subtype(vehicle)):=class:
    var Item:a
    K:string="other"
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t,Y:t where t:subtype(vehicle))<suspends>:t=
    defer:Print("cleanup {Y.N}")
    P:=ca(t){Item:=X}
    Q:=cb(t){Item:=X}
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
