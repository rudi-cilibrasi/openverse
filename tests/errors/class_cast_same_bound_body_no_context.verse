# expect: which a cast gives only as a clause of a failure context
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Hi:int=2}
Add(X:int,Y:int):int=X+Y
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):[]int=
    for(I:=0..1){Add(dup[P].Hi,dup[Q].Hi)+I}
Main():void={}
