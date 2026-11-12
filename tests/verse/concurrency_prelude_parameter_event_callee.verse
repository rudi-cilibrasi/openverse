cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
Apply(event:type{_(:int)<decides>:int}):int=if(X:=event[6]) then X else 0
Main():void=Print("{Apply(Inc)}")
