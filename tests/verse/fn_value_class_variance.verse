# (#724) followup-coerce's value-class-variance: a parameter of type
# type{_(:animal):int}, a function value that is no function's name, passed
# where a type{_(:dog):int} is expected (a contravariant class parameter).
# Epic's Verse compiler admits it, no wrapper needed (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, compiled 2026-11-19); openverse makes
# the value an adapter object that holds it and calls it.
animal := class {}
dog := class(animal) {}

AnyAnimal(A:animal):int = 1
Run(F(:dog):int):int = F(dog{})
Forward(G(:animal):int):int = Run(G)

Main():void =
    Print("value {Forward(AnyAnimal)}")
