# (#724) An event's Subscribe on each kind of event and receiver: a
# sticky_event, which is an event (Subscribe calls nothing at once, only
# later Signals call the function; followup-event/sticky-event-subscribe);
# an event() and a sticky_event() without a value, whose functions take
# none (followup-event/event-unit-subscribe); a type parameter whose bound
# is an event; an event signalled through signalable; and a
# subscribable_event, the openverse extension, which is an event and
# nothing more, cast from and to one
Plain(N:int):void = Print("plain {N}")
Ping():void = Print("ping")
Attach(E:t, F:type{_(:int):void} where t:subtype(event(int)))<transacts>:cancelable = E.Subscribe(F)
Use(S:signalable(int), N:int):void = S.Signal(N)
Main():void =
    S := sticky_event(int){}
    S.Signal(1)
    SS := S.Subscribe(Plain)
    Print("sticky subscribed")
    S.Signal(2)
    SS.Cancel()
    U := event(){}
    SU := U.Subscribe(Ping)
    U.Signal()
    SU.Cancel()
    U.Signal()
    V := sticky_event(){}
    SV := V.Subscribe(Ping)
    V.Signal()
    E := event(int){}
    SE := Attach(E, Plain)
    Use(E, 3)
    SE.Cancel()
    X := subscribable_event(int){}
    SX := Attach(X, Plain)
    Use(X, 4)
    Y:event(int) = X
    if (Z := subscribable_event[Y]) then Z.Signal(5)
    W := subscribable_event(){}
    SW := W.Subscribe(Ping)
    W.Signal()
    Print("done")
