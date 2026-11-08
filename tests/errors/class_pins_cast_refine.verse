# expect: cannot cast a pair(a, b) to dup(a) yet
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
ProbeG(P:pair(a, b) where a:type, b:type):string =
    if (D := dup[P]) then "dup" else "not dup"
Main():void = Print(ProbeG(dup(int){A := 1, B := 2}))
