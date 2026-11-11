# expect: 'Id' is an overloaded method of child
Id(X:t where t:type):t=X
Map(F:type{_(:a):b},X:a where a:type,b:type):b=F(X)
UseGlobal():int=block{F:type{_(:int):int}=Id;F(1)}
reader:=class:
    Id(X:int):string="method {X}"
child:=class(reader):
    Id(X:string):int=X.Length
    Read():string=block{R:=Map(Id,6);R}
Main():void=Print("unused")
