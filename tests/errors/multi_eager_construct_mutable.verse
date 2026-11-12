# expect: constructs an object that has a var field
cell := class<allocates> { var N:int = 0 }
box := struct<allocates> { D:cell = cell{}; V:int }
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Main():void = for (V := R(2)): Print("{V}")
