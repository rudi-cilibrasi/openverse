vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="car"}
truck:=class<allocates>(vehicle){Name:string="truck"}
counter:=class<allocates>{var N:int=0}
Tick(A:[]a,C:counter,Digit:int where a:type)<transacts>:[]a=
    set C.N=C.N*10+Digit
    A
Join(A:[]a,B:[]b,C:counter where a:subtype(vehicle),b:subtype(vehicle))<transacts>:[]vehicle=
    R:=Tick(A,C,1)+Tick(B,C,2)
    R
Wait(A:[]a,B:[]b where a:subtype(vehicle),b:subtype(vehicle))<suspends>:[]vehicle=
    defer:Print("cleanup")
    Sleep(0.1)
    A+B
Launch(A:[]a,B:[]b where a:subtype(vehicle),b:subtype(vehicle)):task([]vehicle)=spawn{Wait(A,B)}
Main()<suspends>:void=
    P:=car{Name:="a"}
    Q:=truck{Name:="b",N:=9}
    A:=array{P}
    B:=array{Q}
    C:=counter{}
    R:=Join(A,B,C)
    if(X:=R[0],Y:=R[1]):
        Print("ordered {R.Length} {X.N} {Y.N} {C.N}")
        set X.N=10
    Print("alias {P.Name} {P.N} {Q.Name} {Q.N}")
    if(Join(A,B,C),false?)then Print("bad")else Print("rollback {C.N}")
    T:=Launch(A,B)
    set P.N=20
    Sleep(0.2)
    V:=T.Await()
    if(X:=V[0],Y:=V[1])then Print("wait {X.N} {Y.N}")
    race:
        Wait(A,B)
        block:
            Sleep(0.05)
            Print("winner")
            Empty:[]vehicle=array{}
            Empty
    Print("cancel {P.N} {Q.N}")
