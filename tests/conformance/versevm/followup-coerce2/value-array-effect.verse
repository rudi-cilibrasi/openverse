# followup-coerce2 (#724): Does UEFN 43.12 refuse an array of
# type{_(:int)<computes>:int} values, held by a local, used as a
# []type{_(:int)<transacts>:int}? (option{...} of a function of another type
# was refused, option-of-fn-default.) OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# []type{_(:int)<computes>:int} as a value of type
# []type{_(:int)<transacts>:int}
Inc(X:int)<computes>:int = X + 1
Dec(X:int)<computes>:int = X - 1
Total(Fs:[]type{_(:int)<transacts>:int})<transacts>:int =
    var Sum:int = 0
    for (F : Fs):
        set Sum += F(10)
    Sum

Main():void =
    Fs:[]type{_(:int)<computes>:int} = array{Inc, Dec}
    Print("OVPROBE total {Total(Fs)}")
