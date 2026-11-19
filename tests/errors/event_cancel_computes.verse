# expect: Stop calls cancelable.Cancel, which has the effect <writes>, which its effects (<computes>) do not allow
# (#724) A subscription's Cancel writes it (Epic's API gives cancelable's
# Cancel <transacts>), so a <computes> function cannot call it
Ping(N:int):void = {}
Stop(S:cancelable)<computes>:void = S.Cancel()
Main():void =
    E := event(int){}
    S := E.Subscribe(Ping)
    Stop(S)
