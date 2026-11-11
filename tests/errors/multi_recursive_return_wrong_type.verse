# expect: the branches have different types: string and int
R(N:int)<computes>:int =
    if(N<=0): return "bad"|1
    N|R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
