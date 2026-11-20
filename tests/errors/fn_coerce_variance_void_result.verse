# expect: using a value of type type{_(:animal):int} as a value of type type{_(:dog):void} is not yet implemented: a function value that is no function named
# (#724) a local of type type{_(:animal):int} used as a
# type{_(:dog):void}: the parameter by class variance, the int result
# discarded, which needs a wrapper (UEFN 43.12, error 3502:
# followup-coerce2's value-void-result).
animal := class {}
dog := class(animal) {}
Count(A:animal):int = 1
Run(F(:dog):void):void = F(dog{})
Main():void =
    G:type{_(:animal):int} = Count
    Run(G)
