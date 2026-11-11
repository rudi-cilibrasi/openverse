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
Lazy(N:int)<computes><decides>:int =
    N > 0
    N | Lazy[N-1]
Main()<transacts><decides>:void =
    K:=kennel{}
    D:=first{V:=K.Get(); V.Bark=8; V}
    Print("first {D.Bark}")
    O:=option{V:=K.Get(); V.Bark=8; V}
    if(V:=O?) then Print("option {V.Bark}")
    if(I:=Lazy[3],V:=K.Get(),I+V.Bark=10) then Print("lazy {I} {V.Bark}")
