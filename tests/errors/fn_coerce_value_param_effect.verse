# expect: using a value of type type{_(:int)<computes>:int} as a value of type type{_(:int)<transacts>:int} is not yet implemented: a function value that is no function named
# (#724) a parameter of type type{_(:int)<computes>:int} passed where a
# type{_(:int)<transacts>:int} is expected: a function value that is no
# function named needs a wrapper to be one of another type, which Epic's
# Verse compiler does not make (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502:
# followup-coerce/value-computes-as-transacts; its control, the parameter
# already <transacts>, is admitted).
Inc(X:int)<computes>:int = X + 1
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<computes>:int)<transacts>:int = Run(G)
Main():void =
    Print("{Forward(Inc)}")
