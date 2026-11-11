# expect: expected dog, found animal
animal := class:
    N:int = 0
    Label():string = "animal"
dog := class(animal):
    Bark:int = 7
    Label<override>():string = "dog"
poodle := class(dog):
    Curl:int = 9
    Label<override>():string = "poodle"
shelter := class:
    Get()<transacts>:animal = animal{N:=1} | animal{N:=2}
kennel := class(shelter):
    Get<override>()<transacts>:dog = dog{N:=3,Bark:=4} | poodle{N:=4,Bark:=8}
NeedDog(D:dog):int = D.Bark
Main()<transacts>:void =
    S:shelter=kennel{}
    for(N:=NeedDog(S.Get())){Print("{N}")}
