# expect: Attach calls event.Subscribe, which has the effect <writes>, which its effects (<computes>) do not allow
# (#724) An event's Subscribe writes the event (Epic's API gives it
# <transacts>), so a <computes> function cannot call it
Ping(N:int):void = {}
Attach(E:event(int))<computes>:cancelable = E.Subscribe(Ping)
Main():void =
    E := event(int){}
    S := Attach(E)
