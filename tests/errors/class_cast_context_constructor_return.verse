# expect: return is not allowed in a constructor (it would skip the items after it)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class{P:pair(a,b);N:int=0}
Make<constructor>(P:pair(a,b) where a:type,b:type):=box(a,b):
    P:=P
    N:=if(D:=dup[P])then block{return 7;D.C}else 0
Main():void=Print("{Make(dup(int){}).N}")
