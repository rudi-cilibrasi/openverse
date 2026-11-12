cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
Main():void=
    subscribable_event:type{_(:int)<decides>:int}=Inc
    if(X:=subscribable_event[6]) then Print("{X}")
