# expect: using a value of type type{_(:animal)<computes>:int} as a value of type type{_(:dog)<transacts>:int} is not yet implemented: a function value that is no function named
# (#724) class variance converts a function value only as it is: a parameter
# of type type{_(:animal)<computes>:int} passed where a
# type{_(:dog)<transacts>:int} is expected also adds effects, which needs a
# wrapper Epic's Verse compiler makes for no value (UEFN 43.12, error 3502:
# followup-coerce's value-computes-as-transacts).
animal := class {}
dog := class(animal) {}
Describe(A:animal)<computes>:int = 1
Run(F(:dog)<transacts>:int):int = F(dog{})
Forward(G(:animal)<computes>:int):int = Run(G)
Main():void = Print("{Forward(Describe)}")
