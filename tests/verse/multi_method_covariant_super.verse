# A super call keeps its selected ancestor declaration and renamed class arguments.
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Bark:int=0 }
shelter(t:type) := class:
    Get(X:t,Y:t)<transacts>:animal(t) = animal(t){V:=X} | animal(t){V:=Y}
kennel(u:type) := class(shelter(u)):
    Get<override>(X:u,Y:u)<transacts>:dog(u) = dog(u){V:=X,Bark:=4} | dog(u){V:=Y,Bark:=8}
child(u:type) := class(kennel(u)):
    Get<override>(X:u,Y:u)<transacts>:dog(u) = (super:)Get(X,Y)
Main()<transacts>:void = for(D:=child(int){}.Get(3,4)){Print("{D.V} {D.Bark}")}
