# expect: expected type{_(:dog):t}, found type{_(:animal):t}: openverse converts a function value by class variance at function types without type parameters only
# (#724) Epic's Verse compiler converts any function value by class variance
# (UEFN 43.12: followup-coerce's value-class-variance); openverse makes the
# adapter that does it for closed function types, as #214's classes for
# names, and not yet in generic code, where a type parameter is in them.
animal := class {}
dog := class(animal) {}
Call(G:type{_(:animal):t}, X:t where t:type):t =
    H:type{_(:dog):t} = G
    H(dog{})
Count(A:animal):int = 1
Main():void = Print("{Call(Count, 2)}")
