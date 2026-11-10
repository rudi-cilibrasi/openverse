# expect: 4:14: cannot infer type parameter t of this call of a function with several values from its arguments
F(X:int where t:type)<transacts>:?t = false | false
Main()<transacts>:void =
    for (V := F(1)) { Print("a") }
