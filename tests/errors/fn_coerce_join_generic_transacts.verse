# expect: using a value of type type{_(:int)<decides><computes>:int} as a value of type type{_(:int)<decides><transacts>:int} is not yet implemented
# the branches of an if are DecidesIdentity <computes><decides> and
# TransactsIdentity <transacts>, both generic, at
# type{_(:int)<decides><transacts>:int}: each needs a wrapper, the first one
# that only widens <computes> to <transacts> (UEFN 43.12, error 3502 at both:
# followup-book2/join-generic-effects-transacts; Function.versetest:271).
DecidesIdentity(X:t where t:type)<computes><decides>:t = X
TransactsIdentity(X:t where t:type)<transacts>:t = X
Pick(Flag:logic)<transacts><decides>:int =
    F:type{_(:int)<decides><transacts>:int} = if (Flag?) { DecidesIdentity } else { TransactsIdentity }
    F[1]
Main():void =
    if (V := Pick[true]):
        Print("{V}")
