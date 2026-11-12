cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
holder:=class:
    event(X:int)<decides>:int=X+1
    Run():int=if(X:=event[6]) then X else 0
Main():void=Print("{holder{}.Run()}")
