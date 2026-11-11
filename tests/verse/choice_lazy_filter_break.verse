# Source breaks cross lazy producers; body loops keep their own breaks.
counter := class:
    var N:int = 0
Trace(H:counter,N:int)<transacts>:int =
    set H.N += 1
    Print("produce {N} {H.N}")
    N
Lazy(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    V := Trace(H,N)
    V | Lazy[H,N-1]
Basic(H:counter)<transacts>:int =
    var Total:int = 0
    defer: Print("basic function {Total}")
    loop:
        defer:
            set Total += 100
            Print("basic loop {Total}")
        for (A := Lazy[H,2], set Total += 10,
            if (A = 1):
                defer: Print("basic filter {Total}")
                break
            else:
                Print("basic keep {A}")):
            set Total += A
            Print("basic body {A} {Total}")
        Print("unexpected basic suffix")
        break
    Total
Double(H:counter)<transacts>:int =
    var Total:int = 0
    loop:
        defer: Print("double loop {Total}")
        for (A := Lazy[H,2], B := Lazy[H,2], set Total += B,
            if (B = 1) then break else Print("double keep {A} {B}")):
            set Total += A
            Print("double body {Total}")
        Print("unexpected double suffix")
        break
    Total
Nested(H:counter)<transacts>:int =
    var Total:int = 0
    loop:
        defer: Print("nested loop {Total}")
        for (A := Lazy[H,2],
            Values := for (B := Lazy[H,2], set Total += B,
                if (B = 1) then break else Print("nested keep {A} {B}")) { B }):
            Print("unexpected nested body")
        Print("unexpected nested suffix")
        break
    Total
Local(H:counter)<transacts>:int =
    var Total:int = 0
    loop:
        for (A := Lazy[H,2], if (A = 0) then break else Print("local keep {A}")):
            loop:
                defer: Print("local body loop")
                set Total += A
                break
            Print("local body after {A}")
        Print("unexpected local suffix")
        break
    Total
Reset(H:counter)<transacts>:int =
    var PassIndex:int = 0
    loop:
        loop:
            for (A := Lazy[H,1], if (A = 0) then break else Print("reset {PassIndex} {A}")):
                Print("reset body {A}")
            Print("unexpected reset suffix")
            break
        set PassIndex += 1
        if (PassIndex = 2):
            break
    PassIndex
WithReturn(H:counter)<transacts>:int =
    loop:
        defer: Print("return loop")
        for (A := Lazy[H,2], if (A = 1) then break else Print("return keep {A}")):
            if (A = 99):
                return A
            Print("return body {A}")
        Print("unexpected return suffix")
        break
    -1
Suspend(H:counter)<suspends>:void =
    loop:
        defer: Print("suspend loop")
        for (A := Lazy[H,2], if (A = 1) then break else Print("suspend keep {A}")):
            Print("suspend body {A}")
            Sleep(0.0)
        Print("unexpected suspend suffix")
        break
Reference(H:counter,UseResult:logic)<suspends>:int =
    Values := array{counter{N:=2},counter{N:=1},counter{N:=0}}
    var Total:int = 0
    loop:
        defer: Print("reference loop {Total}")
        if (UseResult?):
            R := for (E : Values, set Total += E.N,
                if (E.N = 1) then break else Print("reference keep {E.N}")):
                Print("reference body {E.N}")
                E
            Print("unexpected reference result {R.Length}")
        else:
            for (E : Values, set Total += E.N,
                if (E.N = 1) then break else Print("reference keep {E.N}")):
                Print("reference body {E.N}")
        Print("unexpected reference suffix")
        break
    Total
Rollback()<suspends>:int =
    Values := array{counter{N:=1},counter{N:=2},counter{N:=3}}
    var Total:int = 0
    loop:
        defer: Print("rollback loop {Total}")
        for (E : Values, set Total += E.N, Print("rollback probe {E.N}"), E.N > 1,
            if (E.N = 2) then break else Print("rollback keep {E.N}")):
            Print("unexpected rollback body")
        Print("unexpected rollback suffix")
        break
    Total
Main()<suspends>:void =
    H := counter{}
    Print("basic result {Basic(H)}")
    Print("double result {Double(H)}")
    Print("nested result {Nested(H)}")
    Print("local result {Local(H)}")
    Print("reset result {Reset(H)}")
    Print("return result {WithReturn(H)}")
    Suspend(H)
    Print("reference used {Reference(H,true)}")
    Print("reference dropped {Reference(H,false)}")
    Print("rollback result {Rollback()}")
