# expect: prints or calls Err()
R(N:int)<computes>:int =
    Print("bad")
    if(N<=0): return 1|2
    return 10+R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
