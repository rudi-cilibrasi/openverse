small:=type{_X:int where 0<=_X,_X<=10}
counter:=class<allocates>{var N:int=0}
Tick(X:t,C:counter,Digit:int where t:subtype(int))<transacts>:t=
    set C.N=C.N*10+Digit
    X
Format(X:t,C:counter where t:subtype(int))<transacts>:string="{Tick(X,C,1)}:{Tick(X,C,2)}"
Default(X:t,C:counter,?Text:string="{Tick(X,C,1)}" where t:subtype(int))<transacts>:string=Text
Fail(X:t,C:counter where t:subtype(int))<transacts><decides>:t=
    set C.N+=1
    false?
    X
Attempt(X:t,C:counter where t:subtype(int))<transacts>:?string=option{"value {Fail[X,C]}"}
Wait(X:t,C:counter where t:subtype(int))<suspends>:string=
    defer:Print("cleanup {C.N}")
    Sleep(0.1)
    Format(X,C)
Launch(X:t,C:counter where t:subtype(int)):task(string)=spawn{Wait(X,C)}
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
