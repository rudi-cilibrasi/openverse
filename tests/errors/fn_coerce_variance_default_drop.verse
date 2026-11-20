# expect: using a value of type type{_(:animal, ?Loud:int = …):int} as a value of type type{_(:dog):int} is not yet implemented: a function value that is no function named
# (#724) a local whose type has a named parameter with a default, used at a
# type without it and with a class parameter below: dropping the parameter
# needs a wrapper (UEFN 43.12, error 3502: followup-coerce's
# value-default-drop), whatever the variance.
animal := class {}
dog := class(animal) {}
Describe(A:animal, ?Loud:int = 0):int = 1
Run(F(:dog):int):int = F(dog{})
Main():void =
    G:type{_(:animal, ?Loud:int = 0):int} = Describe
    Print("{Run(G)}")
