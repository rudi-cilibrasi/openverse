box(t:type) := class:
    V:t
    Show(X:t):string = "box"
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
Main():void =
    B := box(animal){V := animal{}}
    F:type{_(:dog):string} = B.Show
    Print(F(dog{}))
