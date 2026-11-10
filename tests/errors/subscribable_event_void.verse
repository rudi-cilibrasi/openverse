# expect: subscribable_event(void) is not supported: an event without a value is subscribable_event()
Main():void =
    E := subscribable_event(void){}
    Print("x")
