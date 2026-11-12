# expect: requires convergence
# (#283: R is taken lazily, its choice lifted from the construction in its
# call's argument as the lifter lifts it, so D's computed default runs first
# as an explicit operand, which needs a convergence contract, #511)
Default()<computes>:int =
    Print("default")
    3
box := struct<computes> { D:int = Default(); V:int }
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Main():void = for (V := R(2)): Print("{V}")
