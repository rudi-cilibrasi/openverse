Later(N:int)<suspends>:void=
    Print("nested start {N}")
    Sleep(0.03)
    Print("nested end {N}")
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Sleep(1.0)
ib := class(base(int)):
    Seed:int=7
    Go<override>(?N:int=block{T:=spawn{Later(Seed)};Seed})<suspends>:void=
        defer:Print("body done")
        branch:
            defer:Print("background done")
            Sleep(1.0)
            Print("bad background")
        Print("body start {N}")
        Sleep(1.0)
        Print("bad body")
Start(P:base(t) where t:type)<suspends>:task(void)=
    defer:Print("start done")
    T:=spawn{P.Go()}
    Print("spawned")
    T
Main()<suspends>:void=
    T:=Start(ib{})
    T.Cancel()
    Print("cancelled")
    Sleep(0.1)
