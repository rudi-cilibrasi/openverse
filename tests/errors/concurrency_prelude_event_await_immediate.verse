# expect: suspends: it can only be called in a <suspends> function
Main():void=
    E:=event(int){}
    E.Await()
    Print("bad")
