# followup-variance (#724): Does UEFN 43.12 admit an interface result: a
# local of type type{_():cat} used as a type{_():pet}, cat a class that
# implements the interface pet (covariance through an interface)? Epic
# admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value purr.
# If Epic admits it and prints value purr, OpenVerse agrees. If it refuses
# it (3502), only classes, not interfaces, convert a value's result:
# OpenVerse would refuse it.
pet := interface:
    Purr():string
cat := class(pet):
    Purr<override>():string = "purr"

MakeCat():cat = cat{}
RunPet(F():pet):string = F().Purr()

Main():void =
    G:type{_():cat} = MakeCat
    Print("OVPROBE value {RunPet(G)}")
