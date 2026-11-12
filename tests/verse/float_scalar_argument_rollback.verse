cell:=class{var N:int=0}
From(H:cell):float=block{set H.N+=1;Print("from");2.0}
Bad(H:cell)<decides>:float=block{set H.N+=1;Print("bad");0=1;0.0}
Parameter(H:cell):float=block{set H.N+=1;Print("parameter");0.25}
Main():void=
    H:=cell{}
    if(R:=Lerp(From(H),Bad[H],Parameter(H)),R=0.0):Print("bad success")
    else:Print("failed {H.N}")
