# expect: return is not allowed in a parameter's default
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b),?N:int=if(D:=dup[P])then block{return 7;D.C}else 0 where a:type,b:type):int=N
Call(P:pair(a,b) where a:type,b:type):int=Run(P)
Main():void=Print("{Call(dup(int){})}")
