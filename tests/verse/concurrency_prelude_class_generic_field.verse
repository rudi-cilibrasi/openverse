holder(t:type):=class:
    E:event(t)=event(t){}
Main():void=
    H:=holder(int){}
    H.E.Signal(3)
    Print("ok")
