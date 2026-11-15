# expect: which a cast gives only as a clause of a failure context
# A range's clauses are failure contexts; its body does not gain one.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Hi:int=2}
Bad(P:pair(a,b) where a:type,b:type):[]int=for(I:=0..1){dup[P].Hi+I}
Main():void=Print("{Bad(dup(int){}).Length}")
