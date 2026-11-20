# followup-variance (#724): Does UEFN 43.12 admit class variance beside void
# to true: a local of type type{_(:animal):void} passed where a
# type{_(:dog):true} is expected (the parameter by class variance, the
# result void as true, which the Book's Void.versetest 161-173 has as one
# type)? Epic admits followup-coerce's value-class-variance and
# followup-coerce2's value-class-result, a class parameter and a class
# result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints bark dog, then value done.
# If Epic admits it and prints bark dog, then value done, OpenVerse agrees.
# If it refuses it (3502), void and true together with class variance need a
# wrapper: OpenVerse would refuse it.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

Bark(A:animal):void = Print("OVPROBE bark {A.Name()}")
RunDog(F(:dog):true):void = F(dog{})

Main():void =
    G:type{_(:animal):void} = Bark
    RunDog(G)
    Print("OVPROBE value done")
