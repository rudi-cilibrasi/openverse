# a lazily taken generic call whose arguments are of a class and a subclass: its type argument inferred from the first, the second converted (#235, review of #282)
animal := class:
    Name():string = "animal"
cat := class(animal):
    Name<override>():string = "cat"
Gen(A:t, B:t, N:int where t:type)<decides>:t =
    N > 0
    A | B | Gen[A, B, N - 1]
Main():void =
    X:animal = animal{}
    for (Y := Gen[X, cat{}, 2]) { Print(Y.Name()) }
