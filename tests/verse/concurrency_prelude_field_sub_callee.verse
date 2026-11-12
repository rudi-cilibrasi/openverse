cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
holder:=class:
    subscribable_event:type{_(:int)<decides>:int}=Inc
    Run():int=if(X:=subscribable_event[6]) then X else 0
Main():void=Print("{holder{}.Run()}")
