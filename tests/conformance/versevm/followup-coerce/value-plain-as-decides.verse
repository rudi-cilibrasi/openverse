# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a parameter of type type{_(:int)<computes>:int}) passed
# where a type{_(:int)<computes><decides>:int} is expected? (A name gets the
# wrapper: join-generic-effects-decides-control.) OpenVerse's rule leaves it
# admitted.
# OpenVerse (Lean and C agreeing) prints   value 2
Inc(X:int)<computes>:int = X + 1
Try(F(:int)<computes><decides>:int)<computes><decides>:int = F[1]
Forward(G(:int)<computes>:int)<computes><decides>:int = Try[G]

Main():void =
    if (V := Forward[Inc]):
        Print("OVPROBE value {V}")
