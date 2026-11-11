# expect: kennel.Get must have the signature of shelter.Get
animal := class { N:int=1 }
dog := class(animal) {}
other := class { N:int=2 }
shelter := class:
    Get()<transacts>:animal = animal{} | animal{}
kennel := class(shelter):
    Get<override>()<transacts>:other = other{} | other{}
Main():void = Print("unused")
