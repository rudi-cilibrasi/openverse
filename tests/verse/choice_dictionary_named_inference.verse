ca:=class:
    Infer(?X:u=1 where u:type)<computes>:u=X
    Partial(I:u,?X:u=1 where u:type)<computes>:u=X
cb:=class:
    Infer(?X:u=2 where u:type)<computes>:u=X
    Partial(I:u,?X:u=2 where u:type)<computes>:u=X
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(ca{})|Dup(cb{}))):A.Infer()+B.Infer()
    var Total:int=0
    for(V:Rows):set Total+=V
    Print("{Rows.Length} {Total}")
    Rows2:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(ca{})|Dup(cb{}))):A.Partial(7)+B.Partial(8)
    var Total2:int=0
    for(V:Rows2):set Total2+=V
    Print("{Rows2.Length} {Total2}")
