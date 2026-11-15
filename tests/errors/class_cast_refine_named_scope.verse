# expect: expected b, found a
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Select(?Index:int=0):int=Index
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:b=
    X:=Select(?Index:=if(D:=dup[P])then D.Index else 0)+Select(?Index:=dup[Q].Index)
    P.A
Main():void={}
