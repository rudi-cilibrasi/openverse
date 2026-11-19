# expect: using a value of type type{_(:int)<computes>:int} as a value of type type{_(:int)<transacts>:int} is not yet implemented: this branch of an if
# (#724) the branches of an if, a <computes> and a <transacts> function, at
# type{_(:int)<transacts>:int}: an effect added in a join, no <decides>
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502: followup-coerce/join-computes-transacts).
Inc(X:int)<computes>:int = X + 1
Dec(X:int)<transacts>:int = X - 1
Pick(Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { Inc } else { Dec }
    F(10)
Main():void =
    Print("{Pick(true)}")
