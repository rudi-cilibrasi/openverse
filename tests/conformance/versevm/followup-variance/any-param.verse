# followup-variance (#724): Does UEFN 43.12 admit any as the supertype of a
# parameter: a local of type type{_(:any):int} passed where a
# type{_(:dog):int} is expected? Epic admits followup-coerce's
# value-class-variance and followup-coerce2's value-class-result, a class
# parameter and a class result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse refuses it: expected type{_(:dog):int}, found type{_(:any):int}
# (a function named there is refused too).
# If Epic refuses it (3502), OpenVerse agrees but for the error number. If
# it admits it and prints value 5, a class converts to any as it is in a
# function value's parameter: OpenVerse would make that conversion (its
# adapter discarding the argument), and likewise for a function named there.
animal := class {}
dog := class(animal) {}

TakeAnything(X:any):int = 5
RunDog(F(:dog):int):int = F(dog{})

Main():void =
    G:type{_(:any):int} = TakeAnything
    Print("OVPROBE value {RunDog(G)}")
