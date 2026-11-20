# followup-coerce (#724): Does UEFN 43.12 admit a function value that is no
# function's name (a parameter of type type{_(:animal):int}) passed where a
# type{_(:dog):int} is expected (contravariance, no wrapper)?
# OpenVerse refused it (expected type{_(:dog):int}, found
# type{_(:animal):int}); it now converts the value by an adapter and
# (Lean and C agreeing) prints value 1, as Epic admits.
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
animal := class {}
dog := class(animal) {}

AnyAnimal(A:animal):int = 1
Run(F(:dog):int):int = F(dog{})
Forward(G(:animal):int):int = Run(G)

Main():void =
    Print("OVPROBE value {Forward(AnyAnimal)}")
