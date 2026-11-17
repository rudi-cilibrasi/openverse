Cell:=class{var N:int=0}
Low(H:Cell)<transacts>:int=
    set H.N+=1
    2|1
High(H:Cell)<transacts>:int=
    set H.N+=10
    1|3|4
Choose(H:Cell,Mode:int)<transacts>:int=
    defer:
        set H.N+=1000
        Print("out {H.N}")
    for(I:=Low(H)..High(H)):
        set H.N+=100
        if(Mode=0,I=2):
            var Number:int=H.N
            defer:
                set Number+=7
                set H.N+=1
                Print("number cleanup {Number} {H.N}")
            return Number|block{Print("second number");Number+100}
        if(Mode=1,I=1):
            var Text:string="ab"
            defer:
                set Text+="!"
                set H.N+=1
                Print("text cleanup {Text} {H.N}")
            return Text.Length|block{Print("second text");Text.Length+100}
    0|100
Main()<transacts>:void=
    for(M:array{0,1,2}):
        H:=Cell{}
        for(V:=Choose(H,M)):Print("all {M} {V}")
        Print("state {M} {H.N}")
    A:=Cell{}
    if(V:=Choose(A,0),V=211)then Print("number first {V} {A.N}")else Print("bad")
    B:=Cell{}
    if(V:=Choose(B,1),V=102)then Print("text first {V} {B.N}")else Print("bad")
    C:=Cell{}
    if(V:=Choose(C,1),V=999)then Print("bad")else Print("none {C.N}")
