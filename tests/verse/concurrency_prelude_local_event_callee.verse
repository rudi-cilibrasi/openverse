cancelable:=class{N:int=7}
Inc(X:int)<transacts><decides>:int=X+1
Main():void=
    event:type{_(:int)<transacts><decides>:int}=Inc
    if(X:=event[6]) then Print("{X}")
