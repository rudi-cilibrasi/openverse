pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b) where a:type, b:type):void =
    if (V := if (D := dup[P]) then (option{D.C} | false) else false, N := V?):
        Print("option reverse {N}")
    if (V := if (D := dup[P]) then (array{D.C} | array{D.C + 1}) else array{}, V.Length > 0):
        Print("array {V.Length}")
    if (V := if (D := dup[P]) then (D.C | D.C + 1) else false, true?):
        Print("mixed")
Typed(P:pair(a, b) where a:type, b:type):b =
    if (V := if (D := dup[P]) then (D.A | D.B) else P.B, true?):
        V
    else:
        P.B
Main():void =
    Use(dup(int){A := 1, B := 2})
    Print("typed {Typed(dup(int){A := 1, B := 2})}")
    Print("typed {Typed(pair(int, string){A := 1, B := "s"})}")
