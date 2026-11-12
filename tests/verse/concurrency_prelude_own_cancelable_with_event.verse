cancelable:=class{N:int=7}
Main():void=
    E:=event(int){}
    E.Signal(1)
    Print("{cancelable{}.N}")
