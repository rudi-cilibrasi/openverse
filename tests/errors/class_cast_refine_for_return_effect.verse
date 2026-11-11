# expect: not in a failure context
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
Bad(P:pair(a,b) where a:type,b:type):int =
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        return array{1}[V]
    -1
Main():void = Print("{Bad(dup(int){A:=1,B:=2})}")
