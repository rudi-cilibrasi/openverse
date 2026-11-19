# followup-coerce2 (#724): Does UEFN 43.12 refuse a map whose values are
# type{_(:int)<computes>:int}, held by a local, used as a
# [int]type{_(:int)<transacts>:int}? OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# [int]type{_(:int)<computes>:int} as a value of type
# [int]type{_(:int)<transacts>:int}
Inc(X:int)<computes>:int = X + 1
Look(M:[int]type{_(:int)<transacts>:int})<transacts>:int =
    if (F := M[1]) then F(10) else 0

Main():void =
    M:[int]type{_(:int)<computes>:int} = map{1 => Inc}
    Print("OVPROBE value {Look(M)}")
