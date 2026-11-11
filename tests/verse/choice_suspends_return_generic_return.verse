pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:b =
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        if(B=5)then return P.B
    P.B
Main()<suspends>:void =
    Print("int {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
    Print("string {Use(dup(string){A:="s",B:="t"},dup(int){A:=1,B:=2})}")
