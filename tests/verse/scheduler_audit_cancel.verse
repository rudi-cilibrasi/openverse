state:=class{var N:int=0}
Work(S:state)<suspends>:void=
    defer:
        set S.N+=1
        Print("outer {S.N}")
    block:
        defer:
            set S.N+=10
            Print("inner {S.N}")
        Print("work started")
        Sleep(Inf)
    Print("wrong resumed")
Main()<suspends>:void=
    S:=state{}
    T:=spawn{Work(S)}
    Print("cancel")
    T.Cancel()
    T.Cancel()
    Print("state {S.N}")
