# Aliases of distinct immediate/waiting method results survive completion and cancellation.
cell:=class{var N:int=0}
ra:=class<computes>{K:int}
rb:=class<computes>{K:int}
ca:=class:
    H:cell
    K:int=1
    Read()<reads>:ra=block{Print("pure {H.N}");ra{K:=K}}
cb:=class:
    H:cell
    K:int=2
    Read()<transacts><suspends>:rb=
        defer:Print("leave {H.N}")
        Print("enter {H.N}")
        Sleep(0.1)
        set H.N+=K
        rb{K:=K}
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell)<suspends>:int=
    var Total:int=0
    defer:Print("source {H.N} {Total}")
    branch:
        defer:Print("background {H.N}")
        Sleep(0.05)
        set H.N+=5
        Sleep(100.0)
    Rows:=for(A:=(Dup(ca{H:=H})|Dup(cb{H:=H})),B:=(Dup(1)|Dup("s"))):
        Returned:=A.Read()
        Saved:=Returned
        R:=Saved.K
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
