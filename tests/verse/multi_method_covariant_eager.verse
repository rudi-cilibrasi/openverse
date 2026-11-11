# Covariant recursive dispatch is checked and collected at each declaration result type.
animal := class { N:int }
dog := class(animal) { Bark:int=7 }
shelter := class:
    Get(N:int)<computes>:animal = if(N>0) then (animal{N:=N} | Get(N-1)) else animal{N:=0}
kennel := class(shelter):
    Get<override>(N:int)<computes>:dog = if(N>0) then (dog{N:=N,Bark:=N+10} | Get(N-1)) else dog{N:=0}
All(K:kennel,N:int)<computes>:[]dog = for(D:=K.Get(N)){D}
Main():void =
    K:=kennel{}
    for(D:All(K,2)){Print("{D.N} {D.Bark}")}
    P:shelter=K
    for(D:=P.Get(1)){Print("base {D.N}")}
