# A.Last[] and A.Last[N] (Book of Verse ch. 3): the last element, and the
# one N before it; failing when there is none

Main():void =
    Values := array{10, 20, 30}
    if (V := Values.Last[]) then Print("{V}")
    if (V := Values.Last[0]) then Print("{V}")
    if (V := Values.Last[2]) then Print("{V}")
    if (V := Values.Last[3]) then Print("{V}") else Print("none at 3")
    if (V := Values.Last[-1]) then Print("{V}") else Print("none at -1")
    E:[]int = array{}
    if (V := E.Last[]) then Print("{V}") else Print("empty")
    if (C := "abc".Last[]) then Print("{C}")
