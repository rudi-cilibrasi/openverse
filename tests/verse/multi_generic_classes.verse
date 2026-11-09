# a generic function with several values whose arguments are of sibling classes: its values joined (#235)
animal := class:
    Name():string = "animal"
cat := class(animal):
    Name<override>():string = "cat"
dog := class(animal):
    Name<override>():string = "dog"
Pick(X:t, Y:t where t:type):t = X | Y
Main():void =
    for (A := Pick(cat{}, dog{})) { Print(A.Name()) }
