# expect: F's type has c(…) at its implicit type parameter t, which mutable data holds, c.Data
# The same in a parameter's type (#724): UEFN 43.12 refuses it with 3552
# (followup-book2/parametric-var-where-param; the Book's
# ParametricFunctions.versetest:438).
c(t:type) := class:
    var Data:t
F(X:c(t) where t:type)<transacts>:void = {}
Main():void =
    F(c(int){Data := 1})
