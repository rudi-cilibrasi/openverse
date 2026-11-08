# expect: 12:4: expected type{_(:dog):string}, found type{_(:animal):string}
box(t:type) := class:
    V:t
    Show(X:t):string = "box"
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
Main():void =
    B := box(animal){V := animal{}}
    # (a method of a class with type parameters: at its own type only)
    F:type{_(:dog):string} = B.Show
    Print("x")
