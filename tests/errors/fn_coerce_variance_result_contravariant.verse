# expect: expected type{_():dog}, found type{_():animal}
# (#724) a function value's result converts covariantly only: a
# type{_():animal} is no type{_():dog}.
animal := class {}
dog := class(animal) {}
MakeAnimal():animal = animal{}
Main():void =
    G:type{_():animal} = MakeAnimal
    H:type{_():dog} = G
