# expect: 10:4: kennel.Get returns dog, where shelter.Get, which it overrides and which has several values, returns animal: an override in a family of methods with several values must return the same type (a narrower one is not supported yet, #283)
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
