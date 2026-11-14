pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class{Data:pair(a,b);N:int=0}
Make<constructor>(P:pair(a,b) where a:type,b:type):=box(a,b):
    Data:=P
    N:=if(D:=dup[P])then D.C else 0
Main():void=Print("{Make(dup(int){}).N}")
