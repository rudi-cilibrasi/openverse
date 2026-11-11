root(t:type):=class:
    V:t
    Match(X:u,Y:u where u:subtype(comparable))<decides>:u=block{X=Y;X}
bounded(t:subtype(comparable),u:type):=class(root(t)):
    Extra:u
Use(P:root(t) where t:type):void=
    if(D:=bounded[P]):
        F:type{_(:t,:t)<decides>:t}=D.Match
        if(F[D.V,P.V])then Print("same")else Print("bad")
    else:
        Print("base")
Main():void=
    Use(bounded(int,string){V:=3,Extra:="s"})
    Use(bounded(string,int){V:="s",Extra:=4})
    Use(root(int){V:=1})
