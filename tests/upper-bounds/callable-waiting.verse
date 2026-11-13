worker:=class<allocates>:
    var N:int=0
    Work(D:int)<suspends>:int=
        defer:Print("cleanup {N}")
        set N+=D
        Sleep(0.1)
        N
Keep(F:t where t:subtype(type{_(:int)<suspends>:int}))<computes>:t=F
Apply(F:t,X:int where t:subtype(type{_(:int)<suspends>:int}))<suspends>:int=F(X)
Start(F:t,X:int where t:subtype(type{_(:int)<suspends>:int})):task(int)=spawn{F(X)}
Main()<suspends>:void=
    H:=worker{}
    F:=Keep(H.Work)
    set H.N=10
    T:=Start(F,2)
    Sleep(0.2)
    R:=T.Await()
    Print("task {R}")
    race:
        Apply(F,3)
        block:
            Sleep(0.05)
            Print("winner")
            0
    Print("done {H.N}")
