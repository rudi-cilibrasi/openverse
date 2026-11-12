Probe(E:event(int)):int=if(S:=subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
