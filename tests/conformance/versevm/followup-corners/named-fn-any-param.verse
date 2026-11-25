# followup-corners (#724): A function with an any parameter,
# Ignore(X:any):int, named where a type{_(:int):int} is expected. (followup-
# variance/any-param asks a class below any with a function value; UEFN
# admits a function named at an any result, followup-refused/named-fn-any-
# result.)
# OpenVerse (Lean and C agreeing): refused, expected type{_(:int):int},
# found type{_(:any):int}.
# If Epic refuses it (3502 or 3509), OpenVerse agrees on the verdict. If it
# admits it and prints value 7, a function named converts by contravariance
# from an any parameter: OpenVerse would convert it (an adapter that
# discards the argument).
# Not yet compiled or run by UEFN.
Ignore(X:any):int = 7

Apply(F:type{_(:int):int}):int = F(1)

Main():void =
    Print("OVPROBE value {Apply(Ignore)}")
