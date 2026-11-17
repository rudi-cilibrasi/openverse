Cell:=class<concrete>{var Count:int=0}
Items(H:Cell, Mode:int, I:int)<transacts><decides>:[]int=
    set H.Count+=1
    if(I=1,Mode=0):false?
    if(I=1,Mode=1)then array{} else array{4,7,9}
F(H:Cell,Mode:int)<transacts>:int=
    for(I:=1..2):
        for(J:Items[H,Mode,I]):
            if(I=2,J=7):return J|J+1
    99|100
Main()<transacts>:void=
    for(Mode:array{0,1,2}):
        H:=Cell{}
        for(V:=F(H,Mode)){Print("all {Mode} {V} state {H.Count}")}
        Print("done {Mode} {H.Count}")
    H:=Cell{}
    if(V:=F(H,0),V=8)then Print("first {V} state {H.Count}")else Print("bad")
    R:=Cell{}
    if(V:=F(R,1),V=999)then Print("bad")else Print("rejected state {R.Count}")
