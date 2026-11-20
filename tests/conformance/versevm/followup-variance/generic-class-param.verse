# followup-variance (#724): Does UEFN 43.12 admit a parametric class's
# instance in the parameter: a local of type type{_(:box(animal)):string}
# passed where a type{_(:box(dog)):string} is expected, box(t) covariant in
# t (an immutable field Item:t), so box(dog) is a box(animal)? Epic admits
# followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value dog.
# If Epic admits it and prints value dog, OpenVerse agrees. If it refuses it
# (3502), a parametric class's instances, below by variance, need a wrapper:
# OpenVerse would refuse them in a value's conversion.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
box(t:type) := class:
    Item:t

Unbox(B:box(animal)):string = B.Item.Name()
RunDogBox(F(:box(dog)):string):string = F(box(dog){Item := dog{}})

Main():void =
    G:type{_(:box(animal)):string} = Unbox
    Print("OVPROBE value {RunDogBox(G)}")
