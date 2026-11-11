# Covariant multi-value calls preserve static results and consumer boundaries (#283).
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
Observe(K:kennel)<transacts>:kennel =
    Print("receiver")
    K
Main()<transacts>:void =
    K:=kennel{}
    for(D:=(Observe(K)|Observe(K)).Get()){Print("{D.Bark}")}
