# expect: has the effect <writes>
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Select(?Index:int=0)<transacts>:int=Index
Write()<writes>:int=1
Bad(P:pair(a,b) where a:type,b:type)<computes><decides>:int=Select(?Index:=dup[P].Index+Write())
Main():void={}
