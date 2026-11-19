# followup-coerce (#724): Does UEFN 43.12 admit a function value that is no
# function's name (a parameter of type type{_(:animal):int}) passed where a
# type{_(:dog):int} is expected (contravariance, no wrapper)?
# OpenVerse refuses it: a value of one function type does not convert to
# another by variance (only a named function does, #214). If Epic admits it,
# OpenVerse refuses a valid program. OpenVerse refuses it: expected
# type{_(:dog):int}, found type{_(:animal):int}
animal := class {}
dog := class(animal) {}

AnyAnimal(A:animal):int = 1
Run(F(:dog):int):int = F(dog{})
Forward(G(:animal):int):int = Run(G)

Main():void =
    Print("OVPROBE value {Forward(AnyAnimal)}")
