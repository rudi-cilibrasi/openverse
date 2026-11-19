# followup-coerce (#724): Does UEFN 43.12 admit an if whose branches take a
# class and its subclass, at the function type taking the subclass
# (contravariant parameters, no wrapper)? OpenVerse's rule: admitted.
# OpenVerse (Lean and C agreeing) prints true branch 1 | false branch 2
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
animal := class {}
dog := class(animal) {}

AnyAnimal(A:animal):int = 1
OnlyDog(D:dog):int = 2

Pick(Flag:logic):int =
    F:type{_(:dog):int} = if (Flag?) { AnyAnimal } else { OnlyDog }
    F(dog{})

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
