# Adapter/apply frames retain the original method's cancellation and lifetime.
cell:=class{var N:int=0}
base:=class:
    H:cell
    K:int
    Label:string
    Delay:float
    M(Ignored:t where t:type)<suspends>:int=
        defer:Print("leave {Label} {H.N}")
        Print("enter {Label} {H.N}")
        Sleep(Delay)
        set H.N+=K
        K
ca:=class(base){}
cb:=class(base){}
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell,Delay:float)<suspends>:int=
    var Total:int=0
    defer:Print("source {H.N} {Total}")
    branch:
        defer:Print("background {H.N}")
        Sleep(0.05)
        set H.N+=5
        Sleep(100.0)
    Rows:=for(A:=(Dup(ca{H:=H,K:=1,Label:="a",Delay:=Delay})|Dup(cb{H:=H,K:=2,Label:="b",Delay:=Delay})),B:=(Dup(ca{H:=H,K:=3,Label:="a",Delay:=Delay})|Dup(cb{H:=H,K:=4,Label:="b",Delay:=Delay}))):
        V:=A.M(B)+B.M(A)
        set Total+=1
        V
    Rows.Length
Main()<suspends>:void=
    H:=cell{}
    R:=race:
        Use(H,0.1)
        block{Sleep(0.25);-1}
    Print("result {R} state {H.N}")
    H2:=cell{}
    R2:=Use(H2,0.1)
    Print("result {R2} state {H2.N}")
