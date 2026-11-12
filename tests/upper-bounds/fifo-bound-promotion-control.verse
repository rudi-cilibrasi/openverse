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
            spawn{Waiter(E,X,"task")}
            Sleep(0.0)
            Print("winner")
    set X.N=10
    E.Signal(1)
    Print("signalled")
    Sleep(0.1)
    X
Main()<suspends>:void=
    E:=event(int){}
    C:=car{}
    R:=Racer(C,E)
    Print("done {R.Name} {R.N}")
