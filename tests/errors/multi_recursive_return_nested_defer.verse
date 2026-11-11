# expect: has several values and a defer:, and is recursive
R(N:int)<transacts>:int =
    if(N<=0):
        defer: Print("cleanup")
        return 1|2
    N|R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
