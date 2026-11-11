# Tuple calls preserve instantiated parameter types and call boundaries (#448).
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Code:int }
base(t:type) := class:
    Get(X:t,Y:t)<transacts>:animal(t) = animal(t){V:=X} | animal(t){V:=Y}
mid(u:type) := class(base(u)):
    Get<override>(X:u,Y:u)<transacts>:dog(u) = dog(u){V:=X,Code:=4} | dog(u){V:=Y,Code:=8}
leaf(v:type) := class(mid(v)):
    Get<override>(X:v,Y:v)<transacts>:dog(v) = (super:)Get((X,Y))
Main()<transacts>:void = for(D:=leaf(int){}.Get(3,4)){Print("{D.V} {D.Code}")}