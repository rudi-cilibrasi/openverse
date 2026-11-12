Touch(E:t,N:int where t:subtype(event(int)))<transacts>:int=(E.Signal(N);N)
Default(E:t,?N:int=Touch(E,7) where t:subtype(event(int)))<transacts>:int=N
Main()<transacts>:void=
    E:=event(int){}
    if(Default(E),false?)then Print("bad")else Print("default rolled")
