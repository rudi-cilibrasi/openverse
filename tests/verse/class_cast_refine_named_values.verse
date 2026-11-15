pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Select(?Index:int=0):int=Index
Echo(X:t,?Other:t=X where t:type):t=Other
Direct(P:pair(a,b) where a:type,b:type)<decides>:tuple(b,b)=
    X:=Select(?Index:=dup[P].Index)
    Y:=Echo(P.A,?Other:=dup[P].B)
    (P.A,Y)
Named(P:pair(a,b) where a:type,b:type)<decides>:tuple(b,b)=
    D:=dup[P]
    X:=Select(?Index:=D.Index)
    Y:=Echo(P.A,?Other:=D.B)
    (P.A,Y)
Main():void=
    if(V:=Direct[dup(int){A:=7,B:=9}],W:=Named[dup(int){A:=7,B:=9}])then Print("{V(0)} {V(1)} / {W(0)} {W(1)}")
    if(V:=Direct[dup(string){A:="left",B:="right"}])then Print("{V(0)} {V(1)}")
    if(V:=Direct[pair(int,string){A:=1,B:="other"}])then Print("wrong")else Print("missing")
