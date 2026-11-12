# (#283) Choice points in sequence: a choice after its call of itself in a return, in a <computes> function with a var: taken lazily.
R(N:int)<computes>:int =
    var K:int=0
    if(N<=0): return 1|2
    return 10+R(N-1)+(0|1)
Main():void = for(X:=R(1)): Print("{X}")
