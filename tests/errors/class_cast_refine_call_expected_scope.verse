# expect: expected b, found a
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
Keep(X:t,N:int where t:type):t=X
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:b=Echo(P.A,?Other:=Keep(if(D:=dup[P])then D.B else P.B,dup[Q].Index))
Main():void={}
