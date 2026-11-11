# expect: expected int, found string
R(N:int)<computes>:int =
    if(N<=0): return "bad"|"worse"
    N|R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
