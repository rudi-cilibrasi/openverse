cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
F(subscribable_event:type{_(:int)<decides>:int}):int=if(X:=subscribable_event[6]) then X else 0
G():int=F(Inc)
Main():void=Print("{G()}")
