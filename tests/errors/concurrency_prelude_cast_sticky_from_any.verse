# expect: cannot cast an any to sticky_event
Probe(X:any):int=if(E:=sticky_event[X]) then 1 else 0
Main():void=Print("{Probe(7)}")
