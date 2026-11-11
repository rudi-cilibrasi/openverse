Walk(A:int,B:int,N:int)<transacts><decides>:int =
    var Current:int=A
    if(N>0) then (Current*100+B | Walk[(block{set Current+=10;Current},block{set Current+=1;Current},N-1)] | Current*100+B) else Current*100+B
Main()<transacts>:void =
    var Total:int=0
    if(V:=Walk[1,2,2],set Total+=V,V=1112) then Print("win {V} {Total}")
    if(V:=Walk[1,2,2],set Total+=V,V=9999) then Print("bad") else Print("none {Total}")
