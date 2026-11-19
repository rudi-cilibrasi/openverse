# expect: expected type{_():animal}, found type{_():dog}: openverse converts a function value by class variance only where a function is named (#214)
# (#724) a known difference: a local of type type{_():dog} used as a
# type{_():animal}, and a parameter of type type{_(:animal):int} passed as a
# type{_(:dog):int}, need no wrapper, and Epic's Verse compiler admits both
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086: followup-coerce2/value-class-result,
# followup-coerce/value-class-variance); openverse converts a function value by
# class variance only where a function is named (#214), and refuses them.
animal := class {}
dog := class(animal) {}
MakeDog():dog = dog{}
Run(F():animal):int = 1
Main():void =
    G:type{_():dog} = MakeDog
    Print("{Run(G)}")
