# A narrowed multi-value override retains the static receiver result type (#283).
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
