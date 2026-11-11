# Consecutive cast choices share the remaining consumer clauses.
base := class:
    N:int = 0
child := class(base):
    C:int = 4
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 4
Ordinary(P:base):void =
    if (
        V0 := if (D0 := child[P]) then (D0.C | D0.C + 1) else 0,
        V1 := if (D1 := child[P]) then (D1.C | D1.C + 1) else 0,
        V2 := if (D2 := child[P]) then (D2.C | D2.C + 1) else 0,
        V3 := if (D3 := child[P]) then (D3.C | D3.C + 1) else 0,
        V4 := if (D4 := child[P]) then (D4.C | D4.C + 1) else 0,
        V5 := if (D5 := child[P]) then (D5.C | D5.C + 1) else 0,
        V6 := if (D6 := child[P]) then (D6.C | D6.C + 1) else 0,
        V7 := if (D7 := child[P]) then (D7.C | D7.C + 1) else 0,
        V8 := if (D8 := child[P]) then (D8.C | D8.C + 1) else 0,
        V9 := if (D9 := child[P]) then (D9.C | D9.C + 1) else 0,
        V10 := if (D10 := child[P]) then (D10.C | D10.C + 1) else 0,
        V11 := if (D11 := child[P]) then (D11.C | D11.C + 1) else 0,
        V12 := if (D12 := child[P]) then (D12.C | D12.C + 1) else 0,
        V13 := if (D13 := child[P]) then (D13.C | D13.C + 1) else 0,
        V13 > 4
    ):
        Print("Ordinary {V13}")
Refined(P:pair(a, b) where a:type, b:type):void =
    if (
        V0 := if (D0 := dup[P]) then (D0.C | D0.C + 1) else 0,
        V1 := if (D1 := dup[P]) then (D1.C | D1.C + 1) else 0,
        V2 := if (D2 := dup[P]) then (D2.C | D2.C + 1) else 0,
        V3 := if (D3 := dup[P]) then (D3.C | D3.C + 1) else 0,
        V4 := if (D4 := dup[P]) then (D4.C | D4.C + 1) else 0,
        V5 := if (D5 := dup[P]) then (D5.C | D5.C + 1) else 0,
        V6 := if (D6 := dup[P]) then (D6.C | D6.C + 1) else 0,
        V7 := if (D7 := dup[P]) then (D7.C | D7.C + 1) else 0,
        V8 := if (D8 := dup[P]) then (D8.C | D8.C + 1) else 0,
        V9 := if (D9 := dup[P]) then (D9.C | D9.C + 1) else 0,
        V10 := if (D10 := dup[P]) then (D10.C | D10.C + 1) else 0,
        V11 := if (D11 := dup[P]) then (D11.C | D11.C + 1) else 0,
        V12 := if (D12 := dup[P]) then (D12.C | D12.C + 1) else 0,
        V13 := if (D13 := dup[P]) then (D13.C | D13.C + 1) else 0,
        V13 > 4
    ):
        Print("Refined {V13}")
Main():void =
    Ordinary(child{})
    Refined(dup(int){A := 1, B := 2})
