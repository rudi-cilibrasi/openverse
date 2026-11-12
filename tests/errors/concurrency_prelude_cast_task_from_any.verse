# expect: cannot cast an any to task
Probe(X:any):int=if(T:=task[X]) then 1 else 0
Main():void=Print("{Probe(7)}")
