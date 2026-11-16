# expect: not in a failure context
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Bad(P:pair(a,b) where a:type,b:type):[]b=
    for(V:=if(D:=dup[P])then(D.A|D.B)else P.B) do return array{array{V}}[1]
    array{}
Main():void=Print("{Bad(dup(int){A:=1,B:=2}).Length}")
