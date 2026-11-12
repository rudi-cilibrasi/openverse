pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}
box(a:type,b:type):=class{Data:pair(a,b);N:int=0}
Make<constructor>(P:pair(a,b) where a:type,b:type):=box(a,b):
    Data:=P
    N:=if(V:=if(D:=dup[P])then(D.C|D.C+1)else 0)then V else -1
Main():void=Print("{Make(dup(int){}).N}")
