pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class:
    P:pair(a,b)
    var N:int=0
    block:set N=if(D:=dup[P])then D.C else 0
Run(P:pair(a,b) where a:type,b:type):int=box(a,b){P:=P}.N
Main():void=Print("{Run(dup(int){})}")
