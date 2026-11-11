# expect: expected dog(int), found animal(int)
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Code:int=1 }
base(t:type) := class:
    Pick(X:t,Y:t)<transacts>:animal(t) = animal(t){V:=X} | animal(t){V:=Y}
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u)<transacts>:dog(u) = (super:)Pick((X,Y))
Main()<transacts>:void = for(N:=mid(int){}.Pick(1,2)){Print("{N.Code}")}