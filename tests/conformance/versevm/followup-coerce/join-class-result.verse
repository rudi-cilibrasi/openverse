# followup-coerce (#724): Does UEFN 43.12 admit an if whose branches are
# functions returning a class and its subclass, at the function type
# returning the class (a wrapper-free conversion: the Book's
# FunctionTypes.versetest:198 joins them without an expected type, valid on
# both VMs)? OpenVerse's rule: a reference to a class above needs no
# wrapper, admitted.
# OpenVerse (Lean and C agreeing) prints   true branch dog | false branch
# animal
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

MakeAnimal():animal = animal{}
MakeDog():dog = dog{}

Pick(Flag:logic):string =
    F:type{_():animal} = if (Flag?) { MakeDog } else { MakeAnimal }
    F().Name()

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
