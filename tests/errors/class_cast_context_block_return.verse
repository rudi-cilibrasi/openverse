# expect: return is not allowed in a block: clause (it would skip the clauses after it)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class:
    P:pair(a,b)
    var N:int=0
    block:set N=if(D:=dup[P])then block{return 7;D.C}else 0
Call(P:pair(a,b) where a:type,b:type):int=box(a,b){P:=P}.N
Main():void=Print("{Call(dup(int){})}")
