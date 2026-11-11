Walk(X:t,N:int where t:type)<computes>:int=
    if(N>0)then 1+Walk(array{X},N-1)else 0
Bind(X:t where t:type)<computes>:type{_(:t,:int)<computes>:int}=Walk
Run(X:t where t:type)<computes>:int=
    F:=Bind(X)
    F(X,4)
Main():void=Print("{Run(3)} {Run("word")}")
