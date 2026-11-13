# A registration reached last (then only an empty block: a defer cannot end
# one) yields void; missing branches still fall through.
Last(N:int)<transacts>:void =
    if(N>0):return
    X:=1|2
    defer:Print("last {X}")
    {}
Empty(N:int)<transacts>:any =
    defer:Print("empty")
    if(N>0):
        if(N=1):return 7
        X:=1|2
        Print("body {X}")
Main():void =
    for(Last(1)):Print("early")
    for(Last(0)):Print("value")
    for(N:array{0,1,2}):
        Print("case {N}")
        for(V:=Empty(N)):Print("empty value")
