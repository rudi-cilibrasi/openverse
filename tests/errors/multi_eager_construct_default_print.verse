# expect: it may print
Default()<computes>:int =
    Print("default")
    3
box := struct { D:int = Default(); V:int }
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Main():void = for (V := R(2)): Print("{V}")
