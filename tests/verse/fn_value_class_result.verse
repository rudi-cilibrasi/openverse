# (#724) followup-coerce2's value-class-result: a local of type
# type{_():dog} used as a type{_():animal} (a covariant class result).
# Epic's Verse compiler admits it, no wrapper needed (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, compiled 2026-11-19); openverse makes
# the value an adapter object that holds it and calls it, and the call
# dispatches on the object the value returns.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
MakeDog():dog = dog{}
Run(F():animal):string = F().Name()

Main():void =
    G:type{_():dog} = MakeDog
    Print("value {Run(G)}")
