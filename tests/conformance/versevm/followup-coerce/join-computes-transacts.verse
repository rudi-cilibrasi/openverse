# followup-coerce (#724): Does UEFN 43.12 refuse an if whose branches are a
# <computes> and a <transacts> function, at type{_(:int)<transacts>:int}: an
# effect added in a join, no <decides> (the Book's Function.versetest:271
# and join-generic-effects-transacts add one to generic functions)?
# OpenVerse's rule: a branch of another function type than the if's that
# needs a wrapper is refused, 3502. Control: join-computes-transacts-control
# (both <transacts>).
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
Inc(X:int)<computes>:int = X + 1
Dec(X:int)<transacts>:int = X - 1

Pick(Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { Inc } else { Dec }
    F(10)

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
