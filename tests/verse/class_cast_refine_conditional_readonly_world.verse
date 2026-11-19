box(t:type):=class{A:t}
lit:=class(box(int)){}
pair(a:type,b:type):=class(box(tuple(a,b))){L:box(a);R:box(b)}
Rows(E:box(t) where t:type)<transacts>:[]t=
    Values:=for(V:=if(P:=pair[E],L:=lit[P.L],R:=lit[P.R])then((L.A,R.A)|(L.A+1,R.A))else E.A){V}
    Values
Main():void=
    P:=pair(int,int){A:=(0,0),L:=lit{A:=3},R:=lit{A:=7}}
    for(V:Rows(P)){Print("{V(0)} {V(1)}")}
    for(V:Rows(box(string){A:="fallback"})){Print(V)}
