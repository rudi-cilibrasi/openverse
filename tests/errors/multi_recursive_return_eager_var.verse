# expect: and it has a var or a set
R(N:int)<computes>:int =
    var K:int=0
    if(N<=0): return 1|2
    return 10+R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
