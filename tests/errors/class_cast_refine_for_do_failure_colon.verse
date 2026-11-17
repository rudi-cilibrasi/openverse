# expect: not in a failure context
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Bad(P:pair(a,b) where a:type,b:type):int=
    for(V:=if(D:=dup[P])then(D.A|D.B)else P.B): false?
    0
Main():void=Print("{Bad(dup(int){A:=1,B:=2})}")
