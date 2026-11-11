# expect: has no field 'Code'
animal(t:type) := class { Value:t }
dog(t:type) := class(animal(t)) { Code:int=1 }
base := class:
    Make(X:t where t:type)<transacts>:animal(t) = animal(t){Value:=X}|animal(t){Value:=X}
child := class(base):
    Make<override>(X:u where u:type)<transacts>:dog(u) = dog(u){Value:=X}|dog(u){Value:=X}
Main():void =
    B:base=child{}
    for(V:=B.Make(7)): Print("{V.Code}")
