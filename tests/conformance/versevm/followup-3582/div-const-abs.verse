# 3582 follow-up (#724), compile only: a module constant defined by a call
# of Abs alone. The Book's Runtime API reference declares
# Abs(Value:int)<converges>; in div-const-intrinsic UEFN 43.12 reported only
# Min's call. OpenVerse admits it (Abs converges) and prints "limit 3".
Limit:int = Abs(-3)

Main():void =
    Print("OVPROBE limit {Limit}")
