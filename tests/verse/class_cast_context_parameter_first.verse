pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b),?N:int=if(V:=if(D:=dup[P])then(D.C|D.C+1)else 0)then V else -1 where a:type,b:type):int=N
Call(P:pair(a,b) where a:type,b:type):int=Run(P)
Main():void=Print("{Call(dup(int){})}")
