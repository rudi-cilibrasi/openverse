# expect: F's type has holder(…) at its implicit type parameter t, which mutable data holds, c.Data
# Mutable data reached through another class's field counts (#724):
# holder(t)'s immutable field Inner holds c(t), whose var Data:t is mutable
# data. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses F with
# error 3552, "An implicit type parameter (`t`) used in the type of mutable
# data (`c.Data`) may not be used in the type of a function"
# (followup-book3/parametric-var-where-nested).
c(t:type) := class:
    var Data:t
holder(t:type) := class:
    Inner:c(t)
F(X:t where t:type)<transacts>:holder(t) = holder(t){Inner := c(t){Data := X}}
Main():void =
    Obj := F(1)
