# expect: expected dog, found animal
animal := class { N:int=0 }
dog := class(animal) { Bark:int=7 }
shelter := class:
    Get()<transacts>:animal = animal{} | animal{}
kennel := class(shelter):
    Get<override>()<transacts>:dog = (super:)Get()
Main()<transacts>:void = for(D:=kennel{}.Get()){Print("{D.Bark}")}
