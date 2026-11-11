Pair(X:t where t:type)<computes>:t =
    if(true?): return X|X
    X
Expand(X:t,N:int where t:type)<computes>:t =
    if(N<=0): return Pair(X)
    return Id(Expand(X,N-1))
Id(X:t where t:type)<computes>:t = X
Main():void =
    for(X:=Expand("ok",2)): Print(X)
