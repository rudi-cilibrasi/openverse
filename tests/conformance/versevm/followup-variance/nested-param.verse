# followup-variance (#724): Does UEFN 43.12 admit a nested function type: a
# parameter of type type{_(:type{_():animal}):string} passed where a
# type{_(:type{_():dog}):string} is expected (a parameter that is itself a
# function type, converted contravariantly, its own result covariantly)?
# Epic admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dog.
# If Epic admits it and prints value dog, OpenVerse agrees. If it refuses it
# (3502), Epic's variance of function values stops at one level: OpenVerse
# would refuse a function type nested in a parameter.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
CallMaker(F():animal):string = F().Name()
RunDogMaker(G(F():dog):string):string = G(MakeDog)
Forward(H(F():animal):string):string = RunDogMaker(H)

Main():void =
    Print("OVPROBE value {Forward(CallMaker)}")
