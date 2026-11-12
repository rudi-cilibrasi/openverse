vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string="precise"}
Read(X:t,?V:int=X.N where t:subtype(vehicle))<reads>:int=V
Bump(X:t,Delta:int,?Before:int=Read(X) where t:subtype(vehicle))<transacts>:int=
    set X.N=Before+Delta
    X.N
holder(a:subtype(vehicle)):=class<computes>:
    X:a
    Advance(Delta:int)<transacts>:int=Bump(X,Delta)
Make(X:t where t:subtype(vehicle))<computes>:type{_(:int)<transacts>:int}=holder(t){X:=X}.Advance
Waiter(E:event(int),X:t,Label:string where t:subtype(vehicle))<suspends>:void=
    defer:Print("cleanup {Label} {Read(X)}")
    F:=Make(X)
    V:=E.Await()
    Print("{Label} {V} {F(V)}")
Racer(X:t where t:subtype(vehicle))<suspends>:t=
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
