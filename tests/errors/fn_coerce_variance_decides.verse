# expect: using a value of type type{_(:animal):int} as a value of type type{_(:dog)<decides>:int} is not yet implemented: a function value that is no function named
# (#724) a local of type type{_(:animal):int} used as a
# type{_(:dog)<decides>:int}: class variance and <decides> added, a wrapper
# (UEFN 43.12, error 3502: followup-coerce's value-plain-as-decides).
animal := class {}
dog := class(animal) {}
Count(A:animal):int = 1
Run(F(:dog)<decides>:int):int = 1
Main():void =
    G:type{_(:animal):int} = Count
    Print("{Run(G)}")
