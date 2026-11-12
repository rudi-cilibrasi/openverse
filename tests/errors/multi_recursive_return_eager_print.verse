# expect: prints or calls Err()
# (a choice after its call of itself: all its values computed at a call, F$all, not taken lazily, #246, #283)
R(N:int)<computes>:int =
    Print("bad")
    if(N<=0): return 1|2
    return 10+R(N-1)+(0|1)
Main():void = for(X:=R(1)): Print("{X}")
