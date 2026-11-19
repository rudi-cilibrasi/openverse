# (#724) generic functions named where a function type is expected, with
# effects added: admitted by UEFN 43.12 (followup-book2's
# join-generic-effects-decides-control and -transacts-control; the Book of
# Verse's Function.versetest 217, 231), and a higher-order generic function
# called, not used as a value (generic-higher-order-control).
Identity(X:t where t:type)<computes>:t = X
TransactsIdentity(X:t where t:type)<transacts>:t = X
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Two(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(F(X))
Succ(X:int)<transacts>:int = X + 1
A()<computes><decides>:int =
    F:type{_(:int)<computes><decides>:int} = Identity
    F[1]
B()<transacts><decides>:int =
    F:type{_(:int)<decides><transacts>:int} = TransactsIdentity
    F[2]
Main():void =
    if (X := A[], Y := B[]):
        Print("{X} {Y} {One(Succ, 0)} {Two(Succ, 0)}")
