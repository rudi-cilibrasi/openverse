# expect: the default of field 'Before' of box calls Plain, which might not complete
# Constructor lifting does not bypass the standard default contract.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Plain()<computes>:int=1
box:=class{Before:int=Plain();Value:int}
Bad(P:pair(a,b) where a:type,b:type)<decides>:box=box{Value:=dup[P].C}
Main():void={}
