Keep(E:event(t) where t:type):event(t)=E
Main():void=
    E:=Keep(event(int){})
    E.Signal(8)
    Print("ok")
