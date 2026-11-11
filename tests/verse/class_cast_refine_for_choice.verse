# A selected refining branch keeps its first-generator boundary and body order.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Read(P:pair(a, b), H:counter where a:type, b:type)<transacts>:pair(a, b) =
    set H.N += 1
    P
Trace(Label:string, Value:int)<transacts>:int =
    Print(Label)
    Value
State(P:pair(a, b) where a:type, b:type)<transacts>:void =
    var Total:int = 0
    R := for (A := 1 | 2, set Total += A, Print("prefix {A}"),
        V := if (D := dup[P]):
            Print("selected")
            set Total += 10
            Trace("a", D.C) | Trace("b", D.C + 1)
        else:
            Print("miss")
            0
        , V > 4):
        set Total += V
        Print("body {V} {Total}")
        V
    Print("state {Total} {R.Length}")
LaterEmpty(P:pair(a, b) where a:type, b:type)<transacts>:void =
    var Total:int = 0
    Empty:[]int = array{}
    R := for (A := 1 | 2, set Total += A,
        V := if (D := dup[P]) then (D.C | D.C + 1) else 0,
        set Total += V, W : Empty):
        Print("unexpected {W}")
        V
    Print("empty {Total} {R.Length}")
NoFallback(P:pair(a, b) where a:type, b:type)<transacts>:void =
    H := counter{}
    One := array{1}
    R := for (V := if (D := dup[Read(P, H)]) then (One[D.C] | One[D.C + 1]) else Trace("fallback", 99)):
        Print("value {V}")
        V
    Print("no fallback {H.N} {R.Length}")
Cleanup(P:pair(a, b) where a:type, b:type)<transacts>:void =
    R := for (V := if (D := dup[P]):
        defer: Print("cleanup")
        D.C | D.C + 1
    else:
        0
    , V > 4):
        Print("kept {V}")
        V
    Print("cleaned {R.Length}")
Typed(P:pair(a, b) where a:type, b:type):[]b =
    for (V:b = if (D := dup[P]) then (D.A | D.B) else P.B):
        E:[]b = array{V}
        V
Nested(P:pair(a, b) where a:type, b:type):void =
    for (V := if (false?) then -1 else if (D := dup[P], D.C > 0) then (D.C | D.C + 1) else 0):
        Print("nested {V}")
Main()<transacts>:void =
    Match := dup(int){A := 1, B := 2}
    Miss := pair(int, string){A := 1, B := "s"}
    State(Match)
    State(Miss)
    LaterEmpty(Match)
    LaterEmpty(Miss)
    NoFallback(Match)
    NoFallback(Miss)
    Cleanup(Match)
    Cleanup(Miss)
    for (V : Typed(Match)) { Print("typed {V}") }
    for (V : Typed(Miss)) { Print("typed {V}") }
    Nested(Match)
    Nested(Miss)
