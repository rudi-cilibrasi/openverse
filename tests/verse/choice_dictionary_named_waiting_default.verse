cell:=class{var N:int=0}
Next(H:cell,Tag:string)<transacts><suspends>:int=
    defer:Print("leave {Tag}")
    Sleep(0.1)
    set H.N+=1
    H.N
ca:=class:
    H:cell
    M(?X:int=Next(H,"a"))<transacts><suspends>:int=X
cb:=class:
    H:cell
    M(?X:int=Next(H,"b"))<transacts><suspends>:int=X
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell)<suspends>:int=
    var Total:int=0
    defer:Print("source {Total}")
    Rows:=for(A:=(Dup(ca{H:=H})|Dup(cb{H:=H}))):
        V:=A.M()
        set Total+=1
        Print("body {V} {Total}")
        V
    Rows.Length
Main()<suspends>:void=
    H:=cell{}
    R:=race:
        Use(H)
        block{Sleep(0.25);-1}
    Print("done {R} {H.N}")
    H2:=cell{}
    R2:=Use(H2)
    Print("done {R2} {H2.N}")
