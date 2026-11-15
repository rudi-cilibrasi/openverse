# expect: which a cast gives only as a clause of a failure context
# A case arm is not a failure context merely because its pattern is one.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Bad(P:pair(a,b),N:int where a:type,b:type):int=
    case(N):
        1 => dup[P].C
        _ => 0
Main():void=Print("{Bad(dup(int){},1)}")
