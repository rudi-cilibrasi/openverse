# expect: the default of ?N of Run uses itself (a call of Run that omits ?N)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b),?N:int=if(D:=dup[P])then block{R:=for(V:=(D.C|D.C+1)):Run(P);R.Length}else 0 where a:type,b:type):int=N
Call(P:pair(a,b) where a:type,b:type):int=Run(P)
Main():void=Print("{Call(dup(int){})}")
