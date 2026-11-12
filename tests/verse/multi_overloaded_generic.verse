# Generic overloaded functions with several values (#283), told apart by arity (a type parameter
# overlaps every type): a call takes the overload its arguments fit, its type arguments inferred as
# at any call; one overload calls another of its function's name; one has one value, so a function
# calling only it has one too
Gov(X:t, Y:t where t:type)<transacts>:t = X | Y
Gov(X:int)<transacts>:int = X * 7
Gov(X:t, Y:t, Z:t where t:type)<transacts>:t = Gov(X, Z) | Y
GovOne(X:int)<transacts>:int = Gov(X) + 1
Main()<transacts>:void =
    for (A := Gov(1, 2)) { Print("a {A}") }
    for (A := Gov("p", "q", "r")) { Print("b {A}") }
    Print("c {GovOne(3)}")
    if (A := Gov(4, 5, 6), A > 5) then Print("d {A}")
    for (A := Gov(array{1}, array{2, 3}), B : A) { Print("e {B}") }
