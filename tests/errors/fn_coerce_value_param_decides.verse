# expect: using a value of type type{_(:int)<computes>:int} as a value of type type{_(:int)<decides><computes>:int} is not yet implemented
# (#724) a parameter without <decides> passed where a <computes><decides>
# function is expected: refused (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502:
# followup-coerce/value-plain-as-decides).
Inc(X:int)<computes>:int = X + 1
Try(F(:int)<computes><decides>:int)<computes><decides>:int = F[1]
Forward(G(:int)<computes>:int)<computes><decides>:int = Try[G]
Main():void =
    if (V := Forward[Inc]):
        Print("{V}")
