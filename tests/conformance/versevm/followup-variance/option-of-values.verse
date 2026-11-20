# followup-variance (#724): Does UEFN 43.12 admit an option of a function
# value: a local of type ?type{_():dog} used as a ?type{_():animal}? Epic
# admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dog.
# If Epic admits it and prints value dog, OpenVerse agrees. If it refuses it
# (3502), an option of a function value does not convert by variance:
# OpenVerse would refuse it.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
RunMaybe(O:?type{_():animal}):string =
    if (F := O?) then F().Name() else "none"

Main():void =
    G:type{_():dog} = MakeDog
    O:?type{_():dog} = option{G}
    Print("OVPROBE value {RunMaybe(O)}")
