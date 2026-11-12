cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
F(subscribable_event:type{_(:int)<decides>:int},?N:int=if(X:=subscribable_event[6]) then X else 0):int=N
Main():void=Print("{F(Inc)}")
