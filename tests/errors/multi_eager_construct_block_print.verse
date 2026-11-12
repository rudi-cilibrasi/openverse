# expect: it may print
box := class<computes>:
    D:int = 1+2
    V:int
    block:
        Print("block")
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Main():void = for (V := R(2)): Print("{V}")
