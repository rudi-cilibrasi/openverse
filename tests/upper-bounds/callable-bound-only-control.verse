Apply(F:type{_(:int)<computes>:int})<computes>:int=F(7)
box:=class<computes>:
    Fn:type{_(:int)<computes>:int}
    Run()<computes>:int=Fn(7)
slot:=struct{Fn:type{_(:int)<computes>:int}}
Main():void=Print("bound-only")
