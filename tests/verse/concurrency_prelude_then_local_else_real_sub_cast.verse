Inc(X:int)<decides>:int=X+1
Probe(E:event(int)):int=
    if(subscribable_event:=block{false?;Inc}):
        if(X:=subscribable_event[6]) then X else 0
    else:
        if(S:=subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
