# expect: subscribable_event() is the built-in no-payload shorthand
subscribable_event(t:type):=class{}
Main():void=
    E:=subscribable_event(){}
