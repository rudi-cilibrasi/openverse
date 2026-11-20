# expect: expected type{_(:type{_():animal}):int}, found type{_(:type{_():dog}):int}
# (#724) a parameter of function type converts contravariantly, so its own
# result the other way: a function taking a type{_():dog} is no function
# taking a type{_():animal} (it would be given one returning an animal).
animal := class {}
dog := class(animal) {}
UseDogMaker(F():dog):int = 1
Run(G(F():animal):int):int = 1
Main():void =
    G:type{_(:type{_():dog}):int} = UseDogMaker
    Print("{Run(G)}")
