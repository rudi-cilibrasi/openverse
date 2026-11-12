M:=module:
    event<public>:=class{N:int=7}
Main():void=
    X:(M:)event=(M:)event{}
    E:event(int)=event(int){}
    E.Signal(X.N)
    Print("{X.N}")
