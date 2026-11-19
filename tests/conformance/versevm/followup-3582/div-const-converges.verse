# 3582 follow-up (#724): a module constant defined by a call of a user
# function marked <converges>.
Count()<converges>:int = 3

Limit:int = Count()

Main():void =
    Print("OVPROBE limit {Limit}")
