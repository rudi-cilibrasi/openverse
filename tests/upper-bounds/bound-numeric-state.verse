small:=type{_X:int where 0<=_X,_X<=10}
counter:=class<allocates>{var N:int=0}
Tick(X:t,C:counter,Digit:int where t:subtype(int))<transacts>:t=
    if(Digit=3,X=0)then Err()
    set C.N=C.N*10+Digit
    X
Calc(X:t,Y:u,C:counter where t:subtype(int),u:subtype(int))<transacts>:int=Tick(X,C,1)+Tick(Y,C,2)
Check(X:t,Y:u,Z:v,C:counter where t:subtype(int),u:subtype(int),v:subtype(int))<transacts><decides>:t=Tick(X,C,1)<Tick(Y,C,2)<Tick(Z,C,3)
Divide(X:t,Y:u,C:counter where t:subtype(int),u:subtype(int))<transacts><decides>:rational=Tick(X,C,1)/Tick(Y,C,2)
Wait(X:t,Y:u,C:counter where t:subtype(int),u:subtype(int))<suspends>:int=
    defer:Print("cleanup {C.N}")
    Sleep(0.1)
    Calc(X,Y,C)
Launch(X:t,Y:u,C:counter where t:subtype(int),u:subtype(int)):task(int)=spawn{Wait(X,Y,C)}
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
