# expect: has the effect <writes>
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
Keep(X:t,N:int where t:type):t=X
Write()<writes>:int=1
Bad(P:pair(a,b) where a:type,b:type)<computes><decides>:b=Echo(P.A,?Other:=Keep(dup[P].B,Write()))
Main():void={}
