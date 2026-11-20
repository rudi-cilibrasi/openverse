# expect: expected type{_(:animal):int}, found type{_(:dog):int}
# (#724) a function value's parameter converts contravariantly only: a
# type{_(:dog):int} is no type{_(:animal):int} (it would be called with an
# animal), as a name is not (#214).
animal := class {}
dog := class(animal) {}
OnlyDog(D:dog):int = 1
Run(F(:animal):int):int = F(animal{})
Main():void =
    G:type{_(:dog):int} = OnlyDog
    Print("{Run(G)}")
