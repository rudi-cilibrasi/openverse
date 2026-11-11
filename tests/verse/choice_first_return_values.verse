Two(N:int):int=N|N+1
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=4}
Void(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):void=
    var Total:int=0
    defer:
        set Total+=100
        Print("void cleanup {Total}")
    if(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(F:=dup[Q])then(F.C|F.C+1)else 0,set Total+=A+B,if(A=4)then return else 0):
        Print("void normal {Total}")
Empty(X:t where t:type):[]t=
    defer:Print("empty cleanup")
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=0)then return array{} else 0):
        Print("empty normal")
    array{X}
Normal(X:t where t:type):[]t=
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=99)then return array{} else 0,Extra:t=X,var M:int=A+B):
        set M+=5
        Print("normal {M}")
        return array{Extra}
    array{}
Comparable(X:t where t:subtype(comparable)):[]t=
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=0)then return array{} else 0):
        Print("comparable normal")
    array{X}
Nested(X:t where t:type):[]t=
    defer:Print("nested cleanup")
    for(V:=(Two(0)|Two(2)),W:=(Two(0)|Two(2))):
        if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(V=0)then return array{} else 0):
            Print("nested normal")
    array{X}
Indexed(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):tuple(a,b,c,d)=
    if(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(F:=dup[Q])then(F.C|F.C+1)else 0,if(A=4)then return(P.A,P.B,Q.A,Q.B)else 0):
        Print("indexed normal")
    (P.A,P.B,Q.A,Q.B)
Main():void=
    Void(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
    Print("empty {Empty(7).Length} {Empty(array{1,2}).Length}")
    if(R:=Normal(array{7,8})[0]):Print("payload {R.Length}")
    Print("comparable {Comparable(7).Length}")
    Print("nested {Nested(7).Length}")
    R:=Indexed(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
    Print("indexed {R(0)} {R(1)} {R(2)} {R(3)}")
