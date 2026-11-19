# expect: expected type{_(:int):void}, found type{_():void} (in a call of event.Subscribe)
# (#724) The functions an event(int) calls take its value
Ping():void = {}
Main():void =
    E := event(int){}
    S := E.Subscribe(Ping)
