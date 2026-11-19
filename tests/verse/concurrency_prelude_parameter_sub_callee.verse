cancelable:=class{N:int=7}
Inc(X:int)<transacts><decides>:int=X+1
Apply(subscribable_event:type{_(:int)<transacts><decides>:int}):int=if(X:=subscribable_event[6]) then X else 0
Main():void=Print("{Apply(Inc)}")
