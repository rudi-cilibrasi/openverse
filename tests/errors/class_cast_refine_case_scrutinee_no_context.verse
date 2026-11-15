# expect: which a cast gives only as a clause of a failure context
# Evaluating a case scrutinee does not establish a failure context.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Bad(P:pair(a,b) where a:type,b:type):int=
    case(dup[P].C):
        4 => 1
        _ => 0
Main():void=Print("{Bad(dup(int){})}")
