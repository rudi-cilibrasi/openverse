# expect: their type arguments agree only under a refinement
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Select(?Index:int=0):int=Index
Bad(P:pair(a,b) where a:type,b:type):int=Select(?Index:=dup[P].Index)
Main():void={}
