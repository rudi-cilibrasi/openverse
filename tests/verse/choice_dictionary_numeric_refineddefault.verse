pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=3}
ca:=class{var K:int=1}
cb:=class{var K:rational=1}
Dup(X:t where t:type)<computes>:t=X|X
Echo(P:pair(x,y),?Value:t=if(D:=dup[P])then D.C else 4 where x:type,y:type,t:type)<computes>:t=Value
Use(P:pair(a,b) where a:type,b:type)<transacts>:int=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        R:=set A.K=Echo(P)
        0
    Rows.Length
Main():void=
    Print("{Use(dup(int){A:=1,B:=2})}")
    Print("{Use(pair(int,string){A:=1,B:="s"})}")
