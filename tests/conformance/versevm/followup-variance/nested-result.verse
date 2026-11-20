# followup-variance (#724): Does UEFN 43.12 admit a nested function type in
# the result: a local of type type{_():type{_():dog}} used as a
# type{_():type{_():animal}}? Epic admits followup-coerce's
# value-class-variance and followup-coerce2's value-class-result, a class
# parameter and a class result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dog.
# If Epic admits it and prints value dog, OpenVerse agrees. If it refuses it
# (3502), a function type nested in the result needs a wrapper: OpenVerse
# would refuse it.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
DogMakerMaker():type{_():dog} = MakeDog
RunMakerMaker(G():type{_():animal}):string = G()().Name()

Main():void =
    H:type{_():type{_():dog}} = DogMakerMaker
    Print("OVPROBE value {RunMakerMaker(H)}")
