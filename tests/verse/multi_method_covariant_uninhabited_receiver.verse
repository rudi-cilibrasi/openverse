# Covariant multi-value calls preserve static results and consumer boundaries (#283).
animal(t:type) := class { V:t; Label():string="animal" }
dog(t:type) := class(animal(t)) { Bark:int=7 }
shelter(t:type) := interface:
    Get()<transacts>:animal(t)
kennel := class(shelter(int)):
    Get<override>()<transacts>:dog(int) = dog(int){V:=1} | dog(int){V:=2}
Unused(P:shelter(string))<transacts>:void = for(A:=P.Get()){Print(A.Label())}
Main():void = Print("alive")
