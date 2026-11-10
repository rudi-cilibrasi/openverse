# Casts as later clauses (#243): a chain of fourteen else ifs, each with a cast after a comparison, whose
# code grows with the chain, not twice per link (#400's review: the else was copied into both ifs)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0

F(P:pair(a, b), N:int where a:type, b:type):int =
    if (N = 0, D := dup[P]) then D.C
    else if (N = 1, D1 := dup[P]) then D1.C + 1
    else if (N = 2, D2 := dup[P]) then D2.C + 2
    else if (N = 3, D3 := dup[P]) then D3.C + 3
    else if (N = 4, D4 := dup[P]) then D4.C + 4
    else if (N = 5, D5 := dup[P]) then D5.C + 5
    else if (N = 6, D6 := dup[P]) then D6.C + 6
    else if (N = 7, D7 := dup[P]) then D7.C + 7
    else if (N = 8, D8 := dup[P]) then D8.C + 8
    else if (N = 9, D9 := dup[P]) then D9.C + 9
    else if (N = 10, D10 := dup[P]) then D10.C + 10
    else if (N = 11, D11 := dup[P]) then D11.C + 11
    else if (N = 12, D12 := dup[P]) then D12.C + 12
    else if (N = 13, D13 := dup[P]) then D13.C + 13
    else if (N = 14, D14 := dup[P]) then D14.C + 14
    else -1
Main():void =
    Print("{F(dup(int){A := 1, B := 2, C := 3}, 4)}")
