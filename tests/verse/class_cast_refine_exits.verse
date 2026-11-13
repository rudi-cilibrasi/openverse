# Refining casts whose branch sets vars from outside it and returns or breaks out (#243), the shapes the
# review of #395 found: the vars are set before the caller returns (a defer: sees them), nested casts,
# a failure in a return's or the branch's value is the function's (<decides>, where a return is in
# tail position, Return.versetest:157: a branch of the body's last if), an if as a statement
# with an else
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
DefSet(P:pair(a, b) where a:type, b:type)<transacts>:int =
    var N:int = 1
    defer: Print("defer N={N}")
    if (D := dup[P]):
        set N = D.C
        return N * 10
    N
NestSR(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):int =
    var N:int = 0
    if (D := dup[P]):
        set N += D.C
        if (E := dup[Q]):
            set N += E.C * 10
            if (N > 40) then return N
        set N += 1000
    N
InnerDefer(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<transacts>:int =
    if (D := dup[P]):
        var M:int = 0
        defer: Print("M={M}")
        if (E := dup[Q]):
            set M = E.C
            return 1
        set M = 99
    0
DecRet(P:pair(a, b), Xs:[]int where a:type, b:type)<decides>:int =
    if (D := dup[P]):
        return Xs[D.C]
    else:
        0
DecRetVal(P:pair(a, b), Xs:[]int where a:type, b:type)<decides>:int =
    if (D := dup[P]):
        if (D.C > 0) then return Xs[D.C] else 7
    else:
        8
PlainRet(Xs:[]int, K:int)<decides>:int =
    if (K > 0):
        return Xs[K]
    else:
        0
ValFail(P:pair(a, b), Xs:[]int where a:type, b:type)<decides>:int =
    if (D := dup[P]):
        if (D.C > 50) then return 1 else Xs[D.C]
    else:
        Xs[9]
NoEsc(P:pair(a, b), Xs:[]int where a:type, b:type)<decides>:int =
    X:int = if (D := dup[P]):
        Xs[D.C]
    else:
        Xs[9]
    X
Mid(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[P]):
        if (D.C > 3) then return D.C * 10
    else:
        Print("not dup")
    1
Main()<transacts>:void =
    Print("{DefSet(dup(int){A := 1, B := 2, C := 7})}")
    Print("{DefSet(pair(int, int){A := 1, B := 2})}")
    X := dup(int){A := 1, B := 2, C := 3}
    Y := dup(string){A := "a", B := "b", C := 4}
    Z := pair(int, string){A := 1, B := "x"}
    Print("{NestSR(X, Y)} {NestSR(X, dup(int){A := 1, B := 1, C := 1})} {NestSR(X, Z)} {NestSR(Z, Y)}")
    Print("{InnerDefer(X, Y)}")
    Print("{InnerDefer(X, Z)}")
    Xs := array{10, 20}
    if (V := DecRet[dup(int){A := 1, B := 2, C := 1}, Xs]) then Print("ok {V}") else Print("fail")
    if (V := DecRet[dup(int){A := 1, B := 2, C := 5}, Xs]) then Print("ok {V}") else Print("fail")
    if (V := DecRetVal[dup(int){A := 1, B := 2, C := 5}, Xs]) then Print("ok {V}") else Print("fail")
    if (V := DecRetVal[dup(int){A := 1, B := 2, C := 1}, Xs]) then Print("ok {V}") else Print("fail")
    if (V := PlainRet[Xs, 5]) then Print("plain ok {V}") else Print("plain fail")
    if (V := ValFail[dup(int){A := 1, B := 2, C := 1}, Xs]) then Print("ok {V}") else Print("fail")
    if (V := NoEsc[pair(int, int){A := 1, B := 2}, Xs]) then Print("noesc ok {V}") else Print("noesc fail")
    if (V := ValFail[dup(int){A := 1, B := 2, C := 5}, Xs]) then Print("ok {V}") else Print("fail")

    Print("{Mid(dup(int){A := 1, B := 2, C := 7})}")
    Print("{Mid(pair(int, int){A := 1, B := 2})}")
