# followup-variance (#724): Does UEFN 43.12 admit an array of function
# values: a local of type []type{_():dog}, made of a local's value, used as
# a []type{_():animal} (each element by class variance)? Epic admits
# followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dogdog.
# If Epic admits it and prints value dogdog, OpenVerse agrees. If it refuses
# it (3502), containers of function values do not convert by variance:
# OpenVerse would refuse it (followup-coerce2's value-array-effect refuses
# an array whose elements need a wrapper).
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeDog():dog = dog{}
RunAll(Fs:[]type{_():animal}):string =
    var Out:string = ""
    for (F : Fs):
        set Out += F().Name()
    Out

Main():void =
    G:type{_():dog} = MakeDog
    Gs:[]type{_():dog} = array{G, G}
    Print("OVPROBE value {RunAll(Gs)}")
