# followup-variance (#724): Does UEFN 43.12 admit a map of function values:
# a local of type [int]type{_():dog} used as an [int]type{_():animal}? Epic
# admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value 1dog 2dog.
# If Epic admits it and prints value 1dog 2dog, OpenVerse agrees. If it
# refuses it (3502), a map's function values do not convert by variance:
# OpenVerse would refuse it.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
RunMap(M:[int]type{_():animal}):string =
    var Out:string = ""
    for (K -> F : M):
        set Out += " {K}{F().Name()}"
    Out

Main():void =
    G:type{_():dog} = MakeDog
    M:[int]type{_():dog} = map{1 => G, 2 => G}
    Print("OVPROBE value{RunMap(M)}")
