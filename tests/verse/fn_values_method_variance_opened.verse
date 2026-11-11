root(t:type):=class{V:t}
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)):
    Hidden:b
    Match(X:a)<computes><decides>:tuple(a,int)=
        X=V
        (Hidden,Hidden)
        (X,7)
Bind(B:extra(t,u) where t:subtype(comparable),u:subtype(comparable))<computes>:type{_(:t)<computes><decides>:tuple(t,rational)}=B.Match
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        F:=Bind(D)
        if(R:=F[D.V])then Print("{Floor(R(1))}")else Print("wrong")
    else:
        Print("base")
Main():void=
    Use(extra(string,int){V:="opened",Hidden:=3})
    Use(extra(int,string){V:=9,Hidden:="hidden"})
    Use(root(int){V:=0})
