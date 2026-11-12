M:=module:
    Make<public>():event(int)=event(int){}
Main():void=
    E:=M.Make()
    E.Signal(3)
    Print("ok")
