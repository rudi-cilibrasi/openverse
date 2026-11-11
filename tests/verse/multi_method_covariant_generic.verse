# Covariant calls retain class arguments at both static declaration levels.
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Bark:int = 7 }
shelter(t:type) := class:
    A:animal(t)
    B:animal(t)
    Get()<transacts>:animal(t) = A | B
kennel(t:type) := class(shelter(t)):
    First:dog(t)
    Second:dog(t)
    Get<override>()<transacts>:dog(t) = First | Second
GetDogs(K:kennel(t) where t:type)<transacts>:[]dog(t) = for(D:=K.Get()){D}
GetAnimals(K:shelter(t) where t:type)<transacts>:[]animal(t) = for(D:=K.Get()){D}
Main()<transacts>:void =
    A:=dog(int){V:=1,Bark:=4}
    B:=dog(int){V:=2,Bark:=8}
    K:=kennel(int){A:=A,B:=B,First:=A,Second:=B}
    for(D:GetDogs(K)){Print("{D.V} {D.Bark}")}
    for(D:GetAnimals(K)){Print("{D.V}")}
    X:=dog(string){V:="x",Bark:=5}
    Y:=dog(string){V:="y",Bark:=9}
    S:=kennel(string){A:=X,B:=Y,First:=X,Second:=Y}
    for(D:GetDogs(S)){Print("{D.V} {D.Bark}")}
    for(D:GetAnimals(S)){Print(D.V)}
