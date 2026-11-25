# followup-variance (#724): Does UEFN 43.12 admit a tuple holding a function
# value: a local of type tuple(type{_():dog}, int) used as a
# tuple(type{_():animal}, int)? Epic admits followup-coerce's
# value-class-variance and followup-coerce2's value-class-result, a class
# parameter and a class result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dog 7.
# If Epic admits it and prints value dog 7, OpenVerse agrees. If it refuses
# it (3502), a tuple's function value does not convert by variance:
# OpenVerse would refuse it.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
RunPair(T:tuple(type{_():animal}, int)):string = "{T(0)().Name()} {T(1)}"

Main():void =
    G:type{_():dog} = MakeDog
    T:tuple(type{_():dog}, int) = (G, 7)
    Print("OVPROBE value {RunPair(T)}")
