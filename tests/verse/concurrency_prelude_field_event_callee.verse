cancelable:=class{N:int=7}
Inc(X:int)<transacts><decides>:int=X+1
holder:=class:
    event:type{_(:int)<transacts><decides>:int}=Inc
    Run():int=if(X:=event[6]) then X else 0
Main():void=Print("{holder{}.Run()}")
