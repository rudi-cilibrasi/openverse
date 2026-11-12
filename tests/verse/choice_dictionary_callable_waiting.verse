# A synchronous callback and a suspending callback share the call protocol.
cell:=class{var N:int=0}
Read(H:cell,K:int)<reads>:int=block{Print("pure {H.N}");K}
Wait(H:cell,K:int)<transacts><suspends>:int=
    defer:Print("leave {H.N}")
    Print("enter {H.N}")
    Sleep(0.1)
    set H.N+=K
    K
ca:=class{K:int=1;F:type{_(:cell,:int)<reads>:int}=Read}
cb:=class{K:int=2;F:type{_(:cell,:int)<transacts><suspends>:int}=Wait}
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell)<suspends>:int=
    var Total:int=0
    defer:Print("source {H.N} {Total}")
    branch:
        defer:Print("background {H.N}")
        Sleep(0.05)
        set H.N+=5
        Sleep(100.0)
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):
        R:=A.F(H,A.K)
        set Total+=R
        Print("body {Total} {H.N}")
        R
    Rows.Length
Main()<suspends>:void=
    H:=cell{}
    R:=race:
        Use(H)
        block{Sleep(0.25);-1}
    Print("result {R} state {H.N}")
    H2:=cell{}
    R2:=Use(H2)
    Print("result {R2} state {H2.N}")
