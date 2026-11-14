pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class{X:a;Y:b;N:int=block{P:pair(a,b)=pair(a,b){};if(D:=dup[P])then D.C else 0}}
Field(X:a,Y:b where a:type,b:type):int=box(a,b){X:=X,Y:=Y}.N
Main():void=Print("{Field(7,"s")}")
