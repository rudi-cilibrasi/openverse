# 3582 follow-up (#724): a module constant defined by calls of built-in
# functions (Abs, Min).
Limit:int = Min(Abs(-3), 7)

Main():void =
    Print("OVPROBE limit {Limit}")
