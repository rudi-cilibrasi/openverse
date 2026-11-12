task(t:type):=class{N:int=7}
Main():void=
    T:=task(int){}
    E:=event(int){}
    E.Signal(T.N)
    Print("{T.N}")
