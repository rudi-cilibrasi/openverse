Probe(S:sticky_event(int)):int=if(E:=event[S]) then 1 else 0
Main():void=Print("{Probe(sticky_event(int){})}")
