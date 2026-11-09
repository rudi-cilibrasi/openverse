# expect: 10:4: kennel.Get has several values and returns dog, where shelter.Get returns animal: an override with several values must return the same type, for now (#283)
# (a narrower return type: a dispatch, made before types, has the declaring class's)
animal := class:
    N : int = 1
dog := class(animal):
    Bark : int = 7
shelter := class:
    Get()<transacts>:animal = animal{} | animal{}
kennel := class(shelter):
    Get<override>()<transacts>:dog = dog{} | dog{Bark := 8}
Main()<transacts>:void =
    K : kennel = kennel{}
    for (D := K.Get()):
        Print("{D.Bark}")
