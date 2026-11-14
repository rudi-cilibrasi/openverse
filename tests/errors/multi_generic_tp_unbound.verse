# expect: 5:14: no parameter of F determines its type parameter t
# A function with several values whose type parameter only the result
# names: refused where it is declared (the Book's rule, error 3503; before,
# at the call that could not infer it).
F(X:int where t:type)<transacts>:?t = false | false
Main()<transacts>:void =
    for (V := F(1)) { Print("a") }
