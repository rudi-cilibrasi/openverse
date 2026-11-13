Ident(X:t where t:type)<computes>:t=X
Map(F:type{_(:a)<computes>:b},X:a where a:type,b:type)<computes>:b=F(X)|F(X)
UseGlobal():int=block{F:type{_(:int)<computes>:int}=Ident;F(1)}
reader:=class:
    Id(X:int)<computes>:string="method {X}"
    Read():[]string=for{Map(Id,6)}
child:=class(reader):
    Id(X:string)<computes>:int=X.Length
Main():void=
    R:=reader{}.Read()
    for(S:R):Print(S)
