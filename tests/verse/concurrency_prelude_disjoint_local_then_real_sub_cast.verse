Inc(X:int)<decides>:int=X+1
Probe(E:event(int)):int=
    block:
        subscribable_event:type{_(:int)<decides>:int}=Inc
        if(X:=subscribable_event[6]) then Print("local {X}")
    if(S:=subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
