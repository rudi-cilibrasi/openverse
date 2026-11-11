base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base {N}")
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=block{ branch{ Sleep(0.1); Print("default later") }; Seed })<suspends>:void=
        branch:
            Sleep(0.2)
            Print("method later")
        Print("body {N}")
Run(P:base(t) where t:type)<suspends>:void=
    P.Go()
    Print("returned")
    Sleep(0.15)
    Print("source end")
Main()<suspends>:void=Run(ib{})
