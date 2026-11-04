# Named parameters with defaults (Book of Verse §8.2).
Log(Message:string, ?Level:int = 1, ?Tag:string = "info"):string =
    "[{Tag}:{Level}] {Message}"

Trace(X:int)<transacts>:int =
    Print("evaluating {X}")
    X

Scale(X:int, ?By:int = 2):int = X * By

Main():void =
    Print(Log("started"))
    Print(Log("disk full", ?Tag := "warn", ?Level := 3))
    Print(Log("retry", ?Level := 2))
    Print("{Scale(5)} {Scale(5, ?By := 10)}")
    # positional arguments first, then named ones in the order written
    Print("{Scale(Trace(4), ?By := Trace(3))}")
