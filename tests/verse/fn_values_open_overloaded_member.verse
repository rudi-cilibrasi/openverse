Ident(X:t where t:type):t=X
Map(F:type{_(:a):b},X:a where a:type,b:type):b=F(X)
UseGlobal():int=block{F:type{_(:int):int}=Ident;F(1)}
reader:=class:
    Id(X:int):string="method {X}"
    Read():string=block{R:=Map(Id,6);R}
child:=class(reader):
    Id(X:string):int=X.Length
Main():void=Print(reader{}.Read())
