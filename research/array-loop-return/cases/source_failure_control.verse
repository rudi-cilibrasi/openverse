cell:=class<concrete>:
    var Count:int=0
Items(H:cell,N:int)<transacts><decides>:[]int=
    set H.Count+=1
    if(N<0):false?
    if(N=0)then array{} else if(N=1)then array{4} else array{4,7,9}
ArrayReturn(H:cell,N:int)<transacts>:[]int=
    for(Item:Items[H,N]):
        if(Item=7):return array{Item*10,Item*10+1}
    array{99,100}
Main()<transacts>:void=
    for(N:array{-1,0,1,3}):
        H:=cell{}
        for(V:ArrayReturn(H,N)){Print("all {N} {V} state {H.Count}")}
        Print("final {N} {H.Count}")
    H:=cell{}
    if(K:=0|1,V:=ArrayReturn(H,3)[K],V=71)then Print("first {V} state {H.Count}")else Print("bad first")
    R:=cell{}
    if(K:=0|1,V:=ArrayReturn(R,3)[K],V=900)then Print("bad reject")else Print("reject state {R.Count}")
