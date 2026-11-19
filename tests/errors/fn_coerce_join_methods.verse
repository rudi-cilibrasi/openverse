# expect: using a value of type type{_(:int)<computes>:int} as a value of type type{_(:int)<transacts>:int} is not yet implemented: this branch of an if
# (#724) the branches of an if, an object's <computes> and <transacts>
# methods (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502: followup-coerce/join-method-values).
counter := class:
    Inc(X:int)<computes>:int = X + 1
    Dec(X:int)<transacts>:int = X - 1
Pick(C:counter, Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { C.Inc } else { C.Dec }
    F(10)
Main():void =
    Print("{Pick(counter{}, true)}")
