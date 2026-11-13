Touch(E:event(int),N:int)<transacts>:int=(E.Signal(N);N)
Default(E:event(int),?N:int=Touch(E,7))<transacts>:int=N
Main()<transacts>:void=
    E:=event(int){}
    if(Default(E),false?)then Print("bad")else Print("default rolled")
