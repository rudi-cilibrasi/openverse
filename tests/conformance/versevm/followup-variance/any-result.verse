# followup-variance (#724): Does UEFN 43.12 admit any as the supertype of a
# result: a local of type type{_():dog} used as a type{_():any}? Epic admits
# followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse refuses it: expected type{_():any}, found type{_():dog} (a
# function named there is refused too).
# If Epic refuses it (3502), OpenVerse agrees but for the error number: it
# would cite 3502. If it admits it and prints value called, a class converts
# to any as it is in a function value's result: OpenVerse would make that
# conversion (in Verse Core an any holds no value, so its adapter discards
# the result), and likewise for a function named there.
animal := class {}
dog := class(animal) {}

MakeDog():dog = dog{}
RunAny(F():any):string =
    F()
    "called"

Main():void =
    G:type{_():dog} = MakeDog
    Print("OVPROBE value {RunAny(G)}")
