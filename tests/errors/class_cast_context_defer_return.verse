# expect: return is not allowed in a defer: block
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b) where a:type,b:type):void=
    defer:if(D:=dup[P])then block{return 7;D.C}else 0
Main():void=Run(dup(int){})
