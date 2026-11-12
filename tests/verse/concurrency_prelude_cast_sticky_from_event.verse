Probe(E:event(int)):int=if(S:=sticky_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
