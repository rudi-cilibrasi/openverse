# expect: F's type has s(…) at its implicit type parameter t, which mutable data holds, c.Data
# Mutable data reached through a struct's field counts too (#724): s(t)'s
# field Inner holds c(t), whose var Data:t is mutable data. UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses F with error 3552
# (followup-book4/parametric-var-struct-field).
c(t:type) := class:
    var Data:t
s(t:type) := struct:
    Inner:c(t)
F(X:t where t:type)<transacts>:s(t) = s(t){Inner := c(t){Data := X}}
Main():void =
    Obj := F(1)
