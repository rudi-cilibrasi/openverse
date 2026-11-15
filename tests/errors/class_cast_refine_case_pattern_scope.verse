# expect: the branches have different types: a and b
# A pattern cast does not export its local refinement to the arm.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){C:int=4}
Bad(P:pair(a,b),N:int where a:type,b:type):b=
    case(N):
        dup[P].C => P.A
        _ => P.B
Main():void=Print("{Bad(dup(int){A:=1,B:=2},4)}")
