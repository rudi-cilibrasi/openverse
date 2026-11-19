base := class<concrete>:
    A:int = 1

child := class<abstract>(base):
    B:int

Main():void =
    Print("OVPROBE compiled")
