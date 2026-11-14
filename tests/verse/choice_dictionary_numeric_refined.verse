pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=3}
ca:=class{var K:int=1}
cb:=class{var K:rational=1}
Dup(X:t where t:type)<computes>:t=X|X
Echo(X:t where t:type)<computes>:t=X
Use(P:pair(a,b) where a:type,b:type)<transacts>:int=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        R:=set A.K=if(D:=dup[P])then Echo(D.C) else Echo(4)
        0
    Rows.Length
Main():void=
    Print("{Use(dup(int){A:=1,B:=2})}")
    Print("{Use(pair(int,string){A:=1,B:="s"})}")
