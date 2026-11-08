# expect: subscribable_event(void), an event without a value, is not supported
Main():void =
    E := subscribable_event(void){}
    Print("x")
