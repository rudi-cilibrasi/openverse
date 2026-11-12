state:=class{var N:int=0}
Run(S:state)<suspends>:int=
    defer:
        set S.N+=1000
        Print("function {S.N}")
    branch:
        defer:
            set S.N+=100
            Print("branch {S.N}")
        Print("branch started")
        Sleep(Inf)
    Winner:=race:
        block:
            defer:
                set S.N+=1
                Print("return arm {S.N}")
            Sleep(0.0)
            return 7
        block:
            defer:
                set S.N+=10
                Print("race loser {S.N}")
            Sleep(Inf)
            2
    Winner
Main()<suspends>:void=
    S:=state{}
    R:=Run(S)
    Print("result {R} state {S.N}")
