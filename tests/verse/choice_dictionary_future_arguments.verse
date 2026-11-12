# A method's receiver-dependent result can be known before its argument's type.
cell:=class{var N:int=0}
ca:=class:
    H:cell
    K:int=1
    M(Ignored:u where u:type)<transacts>:ca=
        Print("m a {H.N}")
        set H.N+=K
        Self
cb:=class:
    H:cell
    K:int=2
    M(Ignored:u where u:type)<transacts>:cb=
        Print("m b {H.N}")
        set H.N+=K
        Self
Argument(H:cell,X:u where u:type)<transacts>:u=
    set H.N+=1
    Print("arg {H.N}")
    X
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    Rows:=for(A:=(Dup(ca{H:=H})|Dup(cb{H:=H})),B:=(Dup(ca{H:=H})|Dup(cb{H:=H}))):
        A.M(Argument(H,B)).K+B.M(Argument(H,A)).K
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum} {H.N}")
