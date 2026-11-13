Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
cell:=class{var N:int=0}
ra:=class<computes>{K:int}
rb:=class<computes>{K:int}
WA(H:cell,X:int)<suspends><transacts>:ra=
    defer:Print("call {H.N}")
    Sleep(0.01)
    set H.N+=1
    ra{K:=H.N}
WB(H:cell,X:string)<suspends><transacts>:rb=
    defer:Print("call {H.N}")
    Sleep(0.01)
    set H.N+=1
    rb{K:=H.N}
ca:=class{V:int=7;F:type{_(:cell,:int)<suspends><transacts>:ra}=WA}
cb:=class{V:string="s";F:type{_(:cell,:string)<suspends><transacts>:rb}=WB}
Main()<suspends>:void=
    H:=cell{}
    race:
        block:
            defer:Print("body {H.N}")
            Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):A.F(H,A.V).K+Keep(B)
            Print("wrong {Rows.Length}")
        block:
            Sleep(0.05)
            Print("stop {H.N}")
    Print("after {H.N}")
