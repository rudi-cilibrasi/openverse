# expect: unknown identifier 'D'
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b) where a:type, b:type):void =
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        Print("{D.C}")
Main():void = Use(dup(int){A := 1, B := 2})
