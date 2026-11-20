# followup-variance (#724): Does UEFN 43.12 admit an interface parameter: a
# parameter of type type{_(:pet):string} passed where a type{_(:cat):string}
# is expected, cat a class that implements the interface pet (contravariance
# through an interface, no wrapper)? Epic admits followup-coerce's
# value-class-variance and followup-coerce2's value-class-result, a class
# parameter and a class result of a function value (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value purr.
# If Epic admits it and prints value purr, OpenVerse agrees. If it refuses
# it (3502), Epic converts by class variance but not through interfaces:
# OpenVerse would refuse an interface above or below in a value's
# conversion.
pet := interface:
    Purr():string
cat := class(pet):
    Purr<override>():string = "purr"

Stroke(P:pet):string = P.Purr()
RunCat(F(:cat):string):string = F(cat{})
Forward(G(:pet):string):string = RunCat(G)

Main():void =
    Print("OVPROBE value {Forward(Stroke)}")
