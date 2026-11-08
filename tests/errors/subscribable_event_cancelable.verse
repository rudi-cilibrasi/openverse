# expect: cancelable is the type subscribable_event's Subscribe gives: a program that uses subscribable_event cannot define its own
cancelable := interface:
    Cancel():void
On(X:int):void = Print("{X}")
Main():void =
    E := subscribable_event(int){}
    S := E.Subscribe(On)
