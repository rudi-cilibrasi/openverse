small:=type{_X:int where 0<=_X,_X<=10}
counter:=class<allocates>{var N:int=0}
Tick(X:int,C:counter,Digit:int)<transacts>:int=
    if(Digit=3,X=0)then Err()
    set C.N=C.N*10+Digit
    X
Calc(X:int,Y:int,C:counter)<transacts>:int=Tick(X,C,1)+Tick(Y,C,2)
Check(X:small,Y:int,Z:int,C:counter)<transacts><decides>:small=(Tick(X,C,1)<Tick(Y,C,2)<Tick(Z,C,3);X)
Divide(X:int,Y:int,C:counter)<transacts><decides>:rational=Tick(X,C,1)/Tick(Y,C,2)
Wait(X:int,Y:int,C:counter)<suspends>:int=
    defer:Print("cleanup {C.N}")
    Sleep(0.1)
    Calc(X,Y,C)
Launch(X:int,Y:int,C:counter):task(int)=spawn{Wait(X,Y,C)}
Main()<suspends>:void=
    S:small=3
    C:=counter{}
    Print("arithmetic {Calc(S,4,C)} {C.N}")
    if(Calc(S,4,C),false?)then Print("bad")else Print("rollback {C.N}")
    D:=counter{}
    if(V:=Check[S,5,9,D]):
        Kept:small=V
        Print("chain {Kept} {D.N}")
    E:=counter{}
    if(Check[S,2,0,E])then Print("bad")else Print("short {E.N}")
    if(Divide[S,0,E])then Print("bad")else Print("division rollback {E.N}")
    W:=counter{}
    T:=Launch(S,4,W)
    Sleep(0.2)
    R:=T.Await()
    Print("task {R} {W.N}")
    race:
        Wait(S,4,W)
        block:
            Sleep(0.05)
            Print("winner")
            0
    Print("cancel {W.N}")
