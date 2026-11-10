# Overridden methods with several values of generic classes (#283): a generic interface implemented by generic classes
# (tim-61's expectations, written before the code)
gi(t:type) := interface:
    Get()<transacts>:t
gk(t:type) := class(gi(t)):
    X:t
    Get<override>()<transacts>:t = X | X
gm(t:type) := class(gi(t)):
    X:t
    Y:t
    Get<override>()<transacts>:t = Y
Main()<transacts>:void =
    Is:[]gi(int) = array{gk(int){X := 4}, gm(int){X := 1, Y := 6}}
    for (I : Is, V := I.Get()) { Print("e {V}") }
