F19()<transacts>:int = 1

F24(G()<transacts><decides>:int):int =
    if (X := G[]) then X else 3

Main():void =
    Print("OVPROBE result {F24(F19)}")
