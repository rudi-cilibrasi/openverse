Main():void =
    X:int = 5
    if (Y := int[X]):
        Print("OVPROBE int of int {Y}")
    A:any = 7
    if (Z := int[A]):
        Print("OVPROBE int of any {Z}")
    else:
        Print("OVPROBE int of any failed")
