# expect: which a cast gives only as a clause of a failure context
# An archetype block remains a nonfailable scope inside a failable caller.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box:=class{Value:int}
Bad(P:pair(a,b) where a:type,b:type)<decides>:box=box:
    block:
        X:=dup[P].C
    Value:=0
Main():void={}
