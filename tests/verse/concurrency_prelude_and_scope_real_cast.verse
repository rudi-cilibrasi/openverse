Inc(X:int)<decides>:int=X+1
Probe(E:event(int)):int=
    if((subscribable_event:=Inc) and subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
