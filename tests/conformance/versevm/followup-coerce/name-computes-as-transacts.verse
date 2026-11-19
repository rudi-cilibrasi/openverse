# followup-coerce (#724): Does UEFN 43.12 admit a <computes> function named
# where a type{_(:int)<transacts>:int} is expected, no join and no <decides>
# (the controls of followup-book2 add <decides>)? OpenVerse's rule: a
# function named where a function type is expected gets the wrapper.
# OpenVerse (Lean and C agreeing) prints   value 2
Inc(X:int)<computes>:int = X + 1

Main():void =
    F:type{_(:int)<transacts>:int} = Inc
    Print("OVPROBE value {F(1)}")
