# expect: animal has no field 'Bark'
animal := class { N:int=1 }
dog := class(animal) { Bark:int=7 }
shelter := class:
    Get()<transacts>:animal = animal{} | animal{}
kennel := class(shelter):
    Get<override>()<transacts>:dog = dog{} | dog{Bark:=8}
Bad(S:shelter)<transacts>:int =
    D:=S.Get()
    D.Bark
Main():void = Print("unused")
