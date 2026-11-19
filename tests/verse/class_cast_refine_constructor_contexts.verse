# The same initializer cast works in each enclosing failure context and
# in a constructor function; an unselected case arm does not evaluate it.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box:=class{Value:int}
Opt(P:pair(a,b) where a:type,b:type)<transacts>:?box=option{box{Value:=dup[P].C}}
Cond(P:pair(a,b) where a:type,b:type):int=if(V:=box{Value:=dup[P].C})then V.Value else -1
Collect(Ps:[]pair(a,b) where a:type,b:type)<transacts>:[]int=for(P:Ps,V:=box{Value:=dup[P].C}){V.Value}
First(Ps:[]pair(a,b) where a:type,b:type)<transacts><decides>:box=first{P:Ps;V:=box{Value:=dup[P].C};V.Value>3;V}
Pick(P:pair(a,b),N:int where a:type,b:type)<transacts><decides>:box=case(N){1=>box{Value:=dup[P].C},_=>box{Value:=0}}
Make<constructor>(P:pair(a,b) where a:type,b:type)<transacts><decides>:=box:
    Value:=dup[P].C
Named(P:pair(a,b) where a:type,b:type)<transacts><decides>:box=(D:=dup[P];box{Value:=D.C})
Main():void=
    Good:pair(int,int)=dup(int){}
    Bad:pair(int,int)=pair(int,int){}
    if(V:=Opt(Good)?)then Print("option {V.Value}")
    if(V:=Opt(Bad)?)then Print("wrong")else Print("option missing")
    Print("condition {Cond(Good)} {Cond(Bad)}")
    for(V:Collect(array{Bad,Good,Bad,Good})){Print("for {V}")}
    if(V:=First[array{Bad,Good}])then Print("first {V.Value}")else Print("wrong")
    if(V:=First[array{Bad}])then Print("wrong")else Print("first missing")
    if(V:=Pick[Good,1],W:=Pick[Bad,0])then Print("case {V.Value} {W.Value}")
    if(V:=Pick[Bad,1])then Print("wrong")else Print("case missing")
    if(V:=Make[Good],W:=Named[Good])then Print("constructor {V.Value} {W.Value}")else Print("wrong")
    if(V:=Make[Bad])then Print("wrong")else Print("constructor missing")
