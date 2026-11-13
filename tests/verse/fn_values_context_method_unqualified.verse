Ident(X:t where t:type)<computes>:t=X
UseGlobal():int=block{F:type{_(:int)<computes>:int}=Ident;F(1)}
Apply(F:type{_(:u)<computes>:u},X:u where u:subtype(comparable))<computes>:int=if(F(X)=X)then 1 else -1
box(t:type):=class:
    V:t
    Id(X:u where u:type)<computes>:u=X
    Run(X:u where u:subtype(comparable))<computes>:int=Apply(Id,X)
Main():void=Print("{box(int){V:=7}.Run("method")}")
