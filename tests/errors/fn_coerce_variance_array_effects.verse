# expect: using a value of type []type{_(:animal)<computes>:int} as a value of type []type{_(:dog)<transacts>:int} is not yet implemented: a function value that is no function named
# (#724) an array of function values of type type{_(:animal)<computes>:int}
# used as one of type{_(:dog)<transacts>:int}: each element needs a wrapper
# for the effects (UEFN 43.12, error 3502: followup-coerce2's
# value-array-effect), whatever the variance.
animal := class {}
dog := class(animal) {}
Describe(A:animal)<computes>:int = 1
Run(Fs:[]type{_(:dog)<transacts>:int}):int = Fs.Length
Main():void =
    G:type{_(:animal)<computes>:int} = Describe
    Gs:[]type{_(:animal)<computes>:int} = array{G}
    Print("{Run(Gs)}")
