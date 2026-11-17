cell:=class{var N:int=0}
F(H:cell)<transacts>:int=
    Y:=if(H.N<1)then(1|2)else(return 0)
    defer:set H.N+=1
    Y|Y+1
Main()<transacts>:void=
    H:=cell{}
    for(V:=F(H)){Print("v {V} {H.N}")}
    Print("after")
