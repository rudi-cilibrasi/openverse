Cell:=class{var N:int=0}
Find(H:Cell)<transacts>:int=
    defer:
        set H.N+=100
        Print("function {H.N}")
    for(I:=1..2):
        if(I=2):Err()
        defer:
            set H.N+=10
            Print("range {I} {H.N}")
        loop:
            defer:
                set H.N+=1
                Print("loop {H.N}")
            return H.N|H.N+1
    Err()
Main()<transacts>:void=
    A:=Cell{}
    for(V:=Find(A)):Print("all {V}")
    Print("state {A.N}")
    B:=Cell{}
    if(V:=Find(B),V=1)then Print("first {V}")else Print("missing")
    Print("state {B.N}")
    C:=Cell{}
    if(V:=Find(C),V=999)then Print("missing")else Print("none {C.N}")
