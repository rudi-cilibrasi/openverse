Touch(E:event(int),N:int)<transacts>:int=(E.Signal(N);N)
Main()<transacts>:void=
    E:=event(int){}
    if(Touch(E,7),false?)then Print("bad")else Print("rolled")
