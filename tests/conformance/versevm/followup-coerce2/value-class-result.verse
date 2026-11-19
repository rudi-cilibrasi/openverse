# followup-coerce2 (#724): Does UEFN 43.12 admit a local of type
# type{_():dog} used as a type{_():animal} (a covariant class result, no
# wrapper; followup-coerce's value-class-variance, a contravariant
# parameter, is admitted)? OpenVerse refuses it: a value of one function
# type does not convert to another by variance.
# OpenVerse refuses it: expected type{_():animal}, found type{_():dog}
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
MakeDog():dog = dog{}
Run(F():animal):string = F().Name()

Main():void =
    G:type{_():dog} = MakeDog
    Print("OVPROBE value {Run(G)}")
