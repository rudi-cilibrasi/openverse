Same(X:t where t:type)<computes>:t=X
Show(X:int)<computes>:string="show {X}"
UseGlobal():int=block{F:type{_(:int)<computes>:int}=Same;F(1)}
Map(F:type{_(:int)<computes>:u},X:int where u:type)<computes>:u=F(X)
box:=class:
    Same:type{_(:int)<computes>:string}=Show
    Run():string=Map(Same,6)
Main():void=
    B:=box{}
    R:=Map(B.Same,3)
    Print(R)
    Print(B.Run())
