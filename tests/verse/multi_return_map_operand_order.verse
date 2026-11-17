Cell:=class{var Calls:int=0}
Source(H:Cell,N:int)<transacts><decides>:[string]int=
    set H.Calls+=1
    N>=0
    if(N=0)then map{} else map{"z"=>7,"a"=>3,"b"=>5}
Find(H:Cell,N:int)<transacts>:int=
    for(K -> V:Source[H,N]):
        Print("row {K} {V}")
        if(K="a"):
            defer:Print("cleanup {K}")
            return V|V+K.Length
    99|100
Unindexed()<computes>:int=
    for(V:map{"z"=>5,"a"=>6}):return V|V+1
    0|1
Empty()<transacts>:int=
    var N:int=3
    for(Key -> Item:(block{set N+=10;map{}})):return 1|2
    N|N+1
Main()<transacts>:void=
    for(N:array{-1,0,1}):
        H:=Cell{}
        for(V:=Find(H,N)):Print("all {N} {V}")
        Print("calls {N} {H.Calls}")
    H:=Cell{}
    if(V:=Find(H,1),V=4)then Print("first {V} calls {H.Calls}")else Print("bad")
    R:=Cell{}
    if(V:=Find(R,1),V=999)then Print("bad")else Print("none {R.Calls}")
    for(V:=Unindexed()):Print("unindexed {V}")
    for(V:=Empty()):Print("empty {V}")
