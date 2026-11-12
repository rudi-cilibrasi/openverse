# expect: cannot cast an any to event
Probe(X:any):int=if(E:=event[X]) then 1 else 0
Main():void=Print("{Probe(7)}")
