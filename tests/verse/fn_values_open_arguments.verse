Id(X:t where t:type):t=X
Apply(F:type{_(:t):t},X:t where t:type):t=F(X)
ApplyDefault(X:t,?F:type{_(:t):t}=Id where t:type):t=F(X)
Use(X:t where t:type):t=Apply(Id,X)
Map(F:type{_(:a):b},X:a where a:type,b:type):b=F(X)
Show(X:int):string="show {X}"
Shadow(Id:type{_(:int):string}):string=Map(Id,5)
reader:=class:
    Id:type{_(:int):string}=Show
    Read():string=Map(Id,6)
Logged():int=
    Print("argument")
    4
Main():void=
    Print("{Use(3)}")
    Print("{Apply(Id,Logged())}")
    Print(ApplyDefault("default"))
    Print(Shadow(Show))
    Print(reader{}.Read())
