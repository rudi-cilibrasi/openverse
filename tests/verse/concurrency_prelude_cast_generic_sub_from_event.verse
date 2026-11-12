Probe(E:event(t) where t:type):int=if(S:=subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
