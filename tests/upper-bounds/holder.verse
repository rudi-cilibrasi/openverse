vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
readable:=interface<computes>:
    Read()<computes>:int
holder(t:subtype(vehicle)):=class<computes>(readable):
    X:t
    Read<override>()<computes>:int=X.Speed
Make(X:t where t:subtype(vehicle))<computes>:holder(t)=holder(t){X:=X}
Main():void=
    H:=Make(car{Speed:=9})
    R:readable=H
    Print("holder {R.Read()} {H.X.Name}")
