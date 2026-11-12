M:=module:
    e<public>:=class(event(int)){N:int=7}
Main():void=
    E:(M:)e=(M:)e{}
    E.Signal(3)
    Print("ok")
