# expect: using a value of type type{_(:animal):int} as a value of type type{_(:dog):rational} is not yet implemented: a function value that is no function named
# (#724) a local of type type{_(:animal):int} used as a
# type{_(:dog):rational}: the parameter by class variance, the result int to
# rational, which needs a wrapper (UEFN 43.12, error 3502: followup-coerce2's
# value-int-rational-result).
animal := class {}
dog := class(animal) {}
Count(A:animal):int = 1
Run(F(:dog):rational):int = 1
Main():void =
    G:type{_(:animal):int} = Count
    Print("{Run(G)}")
