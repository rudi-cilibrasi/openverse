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
Racer(X:car)<suspends>:car=
    rush:
        block:
            Sleep(0.0)
            Print("winner")
        block:
            defer:Print("cleanup loser {Read(X)}")
            F:=Make(X)
            Sleep(0.0)
            Print("loser {F(1)}")
    Print("after rush")
    set X.N=10
    Sleep(0.1)
    X
Main()<suspends>:void=
    C:=car{}
    R:=Racer(C)
    Print("done {R.Name} {R.N}")
