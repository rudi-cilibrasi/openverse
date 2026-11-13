vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string="precise"}
Read(X:car,?V:int=X.N)<reads>:int=V
Bump(X:car,Delta:int,?Before:int=Read(X))<transacts>:int=
    set X.N=Before+Delta
    X.N
holder:=class<computes>:
    X:car
    Advance(Delta:int)<transacts>:int=Bump(X,Delta)
Make(X:car)<computes>:type{_(:int)<transacts>:int}=holder{X:=X}.Advance
Waiter(E:event(int),X:car,Label:string)<suspends>:void=
    defer:Print("cleanup {Label} {Read(X)}")
    F:=Make(X)
    V:=E.Await()
    Print("{Label} {V} {F(V)}")
Racer(X:car,E:event(int))<suspends>:car=
    rush:
        block:
            defer:Print("cleanup loser {Read(X)}")
            F:=Make(X)
            V:=E.Await()
            Print("loser {V} {F(V)}")
        block:
            Sleep(0.0)
            Print("winner")
    Print("racer after")
    Sleep(0.0)
    Print("racer done")
    X
Signaller(E:event(int))<suspends>:void=
    Sleep(0.0)
    E.Signal(1)
    Print("signalled")
Main()<suspends>:void=
    E:=event(int){}
    C:=car{}
    T:=spawn{Racer(C,E)}
    spawn{Waiter(E,C,"task")}
    spawn{Signaller(E)}
    set C.N=10
    Sleep(0.1)
    R:=T.Await()
    Print("done {R.Name} {R.N}")
