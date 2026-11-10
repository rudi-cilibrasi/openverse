# expect: 5:14: cannot infer type parameter t of F from the arguments of this call
# (a default `false` cannot give a type parameter its type argument, as at a call, #283)
F(X:int, ?A:?t = false, ?B:t = X where t:type)<transacts>:int = X | X + 1
Main()<transacts>:void =
    for (V := F(1)) { Print("a {V}") }
