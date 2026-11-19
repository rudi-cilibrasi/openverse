F19():int = 1

F23(G():int):int = G()

Main():void =
    Print("OVPROBE result {F23(F19)}")
