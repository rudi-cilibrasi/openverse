pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
Find(P:pair(a,b) where a:type,b:type)<suspends>:int =
    defer: Print("source cleanup")
    for (V0 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        for (V1 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            for (V2 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
                for (V3 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
                    for (V4 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
                        for (V5 := if (D := dup[P]) then (D.C | D.C + 1) else 0):
                            return V0 + V1 + V2 + V3 + V4 + V5
    -1
Main()<suspends>:void = Print("result {Find(dup(int){A:=1,B:=2})}")
