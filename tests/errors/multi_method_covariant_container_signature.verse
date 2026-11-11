# expect: kennel.Get must have the signature of shelter.Get
animal := class { N:int=1 }
dog := class(animal) {}
shelter := class:
    Get()<transacts>:[]animal = array{animal{}} | array{}
kennel := class(shelter):
    Get<override>()<transacts>:[]dog = array{dog{}} | array{}
Main():void = Print("unused")
