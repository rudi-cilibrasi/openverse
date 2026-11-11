Same(X:t where t:subtype(comparable))<computes>:t=X
Twice(F:type{_(:t)<computes>:t},X:t where t:subtype(comparable))<computes>:t=F(X)|F(X)
root(t:type):=class{V:t}
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){Other:b}
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        R:=for(X:=Twice(Same,D.Other)):
            if(X=D.Other)then 1 else 0
        Print("opened {R.Length}")
    else:
        Print("base")
Main():void=
    Use(extra(int,string){V:=7,Other:="s"})
    Use(root(int){V:=3})
