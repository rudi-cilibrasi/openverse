# a generic function with several values at a class type, its arguments of subclasses: its type argument inferred as at a generic call (#235)
animal := class:
    Name():string = "animal"
cat := class(animal):
    Name<override>():string = "cat"
dog := class(animal):
    Name<override>():string = "dog"
Pick(X:t, Y:t where t:type):t = X | Y
Main():void =
    C:animal = cat{}
    D:animal = dog{}
    for (A := Pick(C, D)) { Print(A.Name()) }
