# expect: expected string, found int
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
Keep(X:t,N:int where t:type):t=X
Bad(P:pair(a,b) where a:type,b:type)<decides>:string=Echo(1,?Other:=dup[P].Index)
Main():void={}
