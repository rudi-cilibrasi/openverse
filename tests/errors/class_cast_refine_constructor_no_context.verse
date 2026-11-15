# expect: which a cast gives only as a clause of a failure context
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box:=class{Value:int}
Bad(P:pair(a,b) where a:type,b:type):box=box{Value:=dup[P].C}
Main():void={}
