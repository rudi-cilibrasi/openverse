# expect: Stop calls event.Subscribe, which has the effect <writes>, which its effects (<computes>) do not allow
# (#724) An event()'s Subscribe, whose function takes no value, writes the
# event too (Epic's API gives Subscribe <transacts>); the message names it
# as written, not the compiler's helper
Ping():void = {}
Stop(E:event())<computes>:void =
    S := E.Subscribe(Ping)
Main():void =
    E := event(){}
    Stop(E)
