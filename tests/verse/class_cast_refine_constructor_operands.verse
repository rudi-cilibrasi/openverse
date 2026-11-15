# Multiple constructor operands are lifted in one sequence: the first
# constructor finishes before the second's defaults and cast are evaluated.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Tell(Tag:string,Value:int)<transacts>:int=(Print(Tag);Value)
item:=struct:
    Before:int=Tell("b",1)
    Value:int
late:=struct:
    Before:int=Err()
    Value:int
Sum(X:item,Y:item)<computes>:int=X.Value+Y.Value
Take(X:item,Y:late)<computes>:int=X.Value+Y.Value
Direct(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:int=
    Sum(item{Value:=Tell("x",0)+dup[P].C},item{Value:=Tell("y",0)+dup[Q].C})
Named(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:int=
    B1:=Tell("b",1)
    V1:=Tell("x",0)
    D:=dup[P]
    X:=item{Before:=B1,Value:=V1+D.C}
    B2:=Tell("b",1)
    V2:=Tell("y",0)
    E:=dup[Q]
    Y:=item{Before:=B2,Value:=V2+E.C}
    Sum(X,Y)
Skip(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:int=
    Take(item{Value:=dup[P].C},late{Value:=dup[Q].C})
Main()<transacts>:void=
    Good:pair(int,int)=dup(int){}
    Bad:pair(int,int)=pair(int,int){}
    if(V:=Direct[Good,Good]) then Print("direct {V}") else Print("wrong")
    if(V:=Named[Good,Good]) then Print("named {V}") else Print("wrong")
    if(V:=Direct[Good,Bad]) then Print("wrong") else Print("missing")
    if(V:=Named[Good,Bad]) then Print("wrong") else Print("missing named")
    if(V:=Skip[Bad,Good]) then Print("wrong") else Print("skipped later default")
