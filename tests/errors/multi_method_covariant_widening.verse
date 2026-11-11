# expect: wide.Get must have the signature of kennel.Get
animal := class { N:int=1 }
dog := class(animal) { Bark:int=7 }
shelter := class:
    Get()<transacts>:animal = animal{} | animal{}
kennel := class(shelter):
    Get<override>()<transacts>:dog = dog{} | dog{}
wide := class(kennel):
    Get<override>()<transacts>:animal = animal{} | animal{}
Main():void = Print("unused")
