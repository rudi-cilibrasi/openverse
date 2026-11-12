cell:=class{var N:int=0}
From(H:cell):float=block{set H.N+=1;Print("from {H.N}");2.0}
To(H:cell):float=block{set H.N+=1;Print("to {H.N}");8.0}
Parameter(H:cell):float=block{set H.N+=1;Print("parameter {H.N}");0.25}
Main():void=
    H:=cell{}
    R:=Lerp(From(H),To(H),Parameter(H))
    Print("result {R} calls {H.N}")
