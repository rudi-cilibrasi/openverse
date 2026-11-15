# expect: declared construction budget
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box:=class<reads>{Value:int}
Bad(P:pair(a,b) where a:type,b:type)<computes><decides>:int=box{Value:=dup[P].C}.Value
Main():void={}
