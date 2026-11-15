# expect: expected b, found a
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
Keep(X:t,N:int where t:type):t=X
Bad(P:pair(a,b) where a:type,b:type):b=Echo(P.A,?Other:=dup[P].B)
Main():void={}
