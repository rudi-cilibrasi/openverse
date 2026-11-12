cell:=class{var N:int=0}
ca:=class:
    H:cell
    var Data:[int]int=map{}
    Key()<transacts><suspends>:int=
        Sleep(0.1)
        Print("key a")
        set H.N+=1
        7
    RHS()<transacts><suspends>:int=
        defer:Print("leave a")
        Sleep(0.1)
        Print("rhs a")
        set H.N+=10
        set Data=map{9=>900}
        3
cb:=class:
    H:cell
    var Data:[string]int=map{}
    Key()<transacts><suspends>:string=
        Sleep(0.1)
        Print("key b")
        set H.N+=1
        "k"
    RHS()<transacts><suspends>:int=
        defer:Print("leave b")
        Sleep(0.1)
        Print("rhs b")
        set H.N+=10
        set Data=map{"z"=>900}
        3
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell)<suspends>:int=
    var Total:int=0
    defer:Print("source {Total} {H.N}")
    Rows:=for(A:=(Dup(ca{H:=H})|Dup(cb{H:=H}))):
        V:=set A.Data[A.Key()]=A.RHS()
        set Total+=1
        Print("body {V} {H.N}")
        V
    Rows.Length
Main()<suspends>:void=
    H:=cell{}
    R:=race:
        Use(H)
        block{Sleep(0.55);-1}
    Print("done {R} {H.N}")
    H2:=cell{}
    R2:=Use(H2)
    Print("done {R2} {H2.N}")
