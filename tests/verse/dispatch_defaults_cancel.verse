base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=block{ defer{Print("default done")};branch{defer{Print("background stop")};Sleep(1.0);Print("bad background")};Seed })<suspends>:void=
        defer:Print("body stop")
        Print("body start {N}")
        Sleep(1.0)
Work(P:base(t) where t:type)<suspends>:void=
    defer:Print("source stop")
    P.Go()
    Print("bad after")
Main()<suspends>:void=
    race:
        Work(ib{})
        block{Sleep(0.1);Print("cancel")}
