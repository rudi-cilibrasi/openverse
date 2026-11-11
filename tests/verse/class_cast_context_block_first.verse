pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}
box(a:type,b:type):=class:
    P:pair(a,b)
    var N:int=0
    block:set N=if(V:=if(D:=dup[P])then(D.C|D.C+1)else 0)then V else -1
Run(P:pair(a,b) where a:type,b:type):int=box(a,b){P:=P}.N
Main():void=Print("{Run(dup(int){})}")
