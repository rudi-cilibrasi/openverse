cancelable:=class{N:int=7}
Inc(X:int)<decides>:int=X+1
Main():void=
    event:type{_(:int)<decides>:int}=Inc
    if(X:=event[6]) then Print("{X}")
