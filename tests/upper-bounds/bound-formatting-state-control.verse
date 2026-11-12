small:=type{_X:int where 0<=_X,_X<=10}
counter:=class<allocates>{var N:int=0}
Tick(X:int,C:counter,Digit:int)<transacts>:int=
    set C.N=C.N*10+Digit
    X
Format(X:int,C:counter)<transacts>:string="{Tick(X,C,1)}:{Tick(X,C,2)}"
Default(X:int,C:counter,?Text:string="{Tick(X,C,1)}")<transacts>:string=Text
Fail(X:int,C:counter)<transacts><decides>:int=
    set C.N+=1
    false?
    X
Attempt(X:int,C:counter)<transacts>:?string=option{"value {Fail[X,C]}"}
Wait(X:int,C:counter)<suspends>:string=
    defer:Print("cleanup {C.N}")
    Sleep(0.1)
    Format(X,C)
Launch(X:int,C:counter):task(string)=spawn{Wait(X,C)}
Main()<suspends>:void=
    S:small=3
    C:=counter{}
    Print("format {Format(S,C)} {C.N}")
    if(Format(S,C),false?)then Print("bad")else Print("rollback {C.N}")
    if(Attempt(S,C)?)then Print("bad")else Print("failed source {C.N}")
    D:=counter{}
    Print("default {Default(S,D)} {D.N}")
    W:=counter{}
    T:=Launch(S,W)
    Sleep(0.2)
    R:=T.Await()
    Print("task {R} {W.N}")
    race:
        Wait(S,W)
        block:
            Sleep(0.05)
            Print("winner")
            ""
    Print("cancel {W.N}")
