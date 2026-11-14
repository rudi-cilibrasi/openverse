# Returns must cross lazy loops before leaving their source loop. (Failure
# cannot leave one: a loop's body is no failure context, also in a <decides>
# function, Book of Verse tests, SOL-4199-BreakFromIf.versetest:79.)
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
counter := class:
    var N:int = 0
Lazy(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("lazy {N} {H.N}")
    N | Lazy[H,N-1]
Single(P:pair(a,b),H:counter where a:type,b:type)<suspends>:int =
    Sleep(0.01)
    var Total:int = 0
    defer: Print("single source {Total}")
    loop:
        defer: Print("single loop {Total}")
        for (L := Lazy[H,2], V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            defer: Print("single body {Total}")
            set Total += L + V
            return Total
        Print("unexpected single suffix")
        break
    -1
Double(P:pair(a,b),H:counter where a:type,b:type)<suspends>:int =
    Sleep(0.01)
    var Total:int = 0
    defer: Print("double source {Total}")
    loop:
        defer: Print("double loop {Total}")
        for (L := Lazy[H,2], K := Lazy[H,2],
            V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            defer: Print("double body {Total}")
            set Total += L + K + V
            return Total
        Print("unexpected double suffix")
        break
    -1
Main()<suspends>:void =
    P := dup(int){A:=1,B:=2}
    H := counter{}
    Print("single result {Single(P,H)}")
    Print("double result {Double(P,H)}")
