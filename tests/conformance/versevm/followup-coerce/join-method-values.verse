# followup-coerce (#724): Does UEFN 43.12 refuse an if whose branches are an
# object's <computes> method and its <transacts> one, at
# type{_(:int)<transacts>:int}? OpenVerse's rule: refused, 3502, as for
# functions. Control: join-method-values-control (both <transacts>).
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
counter := class:
    Inc(X:int)<computes>:int = X + 1
    Dec(X:int)<transacts>:int = X - 1

Pick(C:counter, Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { C.Inc } else { C.Dec }
    F(10)

Main():void =
    C := counter{}
    Print("OVPROBE true branch {Pick(C, true)}")
    Print("OVPROBE false branch {Pick(C, false)}")
