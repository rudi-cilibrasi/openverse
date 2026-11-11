# Recursive covariant calls carry the same generic receiver/result witnesses.
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Bark:int=7 }
shelter(t:type) := class:
    Get(N:int,X:t)<computes>:animal(t) = if(N>0) then (animal(t){V:=X}|Get(N-1,X)) else animal(t){V:=X}
kennel(t:type) := class(shelter(t)):
    Get<override>(N:int,X:t)<computes>:dog(t) = if(N>0) then (dog(t){V:=X,Bark:=N+10}|Get(N-1,X)) else dog(t){V:=X}
All(K:kennel(t),X:t where t:type)<computes>:[]dog(t) = for(D:=K.Get(2,X)){D}
Main():void =
    for(D:All(kennel(int){},7)){Print("{D.V} {D.Bark}")}
    for(D:All(kennel(string){},"s")){Print("{D.V} {D.Bark}")}
