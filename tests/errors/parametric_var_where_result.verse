# expect: F's type has c(…) at its implicit type parameter t, which mutable data holds, c.Data
# A generic function's type may not apply a class with a var field of its
# parameter to an implicit type parameter (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses it with error 3552, "An
# implicit type parameter (`t`) used in the type of mutable data (`c.Data`)
# may not be used in the type of a function"
# (followup-book2/parametric-var-where-construct; the Book's tests,
# ParametricFunctions.versetest:431).
c(t:type) := class:
    var Data:t
F(X:t where t:type)<transacts>:c(t) = c(t){Data := X}
Main():void =
    Obj := F(1)
