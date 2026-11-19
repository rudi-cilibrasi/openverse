# expect: the value of the constant Big calls Next, which might not complete
# A <computes> function is no <converges> one (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses the call, error 3582
# (followup-int/int-module-const-call of the integers branch).
Next(N:int)<computes>:int = N + 1
Big:int = Next(41)
Main():void = Print("{Big}")
