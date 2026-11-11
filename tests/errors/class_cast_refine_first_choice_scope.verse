# expect: unknown identifier 'D'
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b) where a:type, b:type):void =
    if (V := if (D := dup[P]) then (D.C | D.C + 1) else 0, D.C > 0):
        Print("{V}")
Main():void = Use(dup(int){A := 1, B := 2})
