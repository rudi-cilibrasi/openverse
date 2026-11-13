Apply(F:t where t:subtype(type{_(:int)<computes>:int}))<computes>:int=F(7)
box(a:subtype(type{_(:int)<computes>:int})):=class<computes>:
    Fn:a
    Run()<computes>:int=Fn(7)
slot(a:subtype(type{_(:int)<computes>:int})):=struct{Fn:a}
Main():void=Print("bound-only")
