# followup-variance (#724): Does UEFN 43.12 admit a method's value: a local
# of type type{_(:animal):int} bound to C.Bump, a method that counts its
# calls in its object, passed where a type{_(:dog):int} is expected? Epic
# admits followup-coerce's value-class-variance and followup-coerce2's
# value-class-result, a class parameter and a class result of a function
# value (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19).
# OpenVerse (Lean and C agreeing) prints value 1 2 2.
# If Epic admits it and prints value 1 2 2 (both calls reach the one
# object), OpenVerse agrees; another count would mean the receiver is
# copied. If it refuses it (3502), a bound method's value does not convert
# by variance: OpenVerse would refuse it.
animal := class {}
dog := class(animal) {}
counter := class:
    var Count:int = 0
    Bump(A:animal):int =
        set Count += 1
        Count

RunDog(F(:dog):int):int = F(dog{})

Main():void =
    C:counter = counter{}
    G:type{_(:animal):int} = C.Bump
    First := RunDog(G)
    Second := RunDog(G)
    Print("OVPROBE value {First} {Second} {C.Count}")
