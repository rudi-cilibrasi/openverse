# 3582 follow-up (#724): a module constant defined by operators and a
# failable expression with a default. Control for calls.
Base:int = 6
Half:int = Floor(Base / 4) or 0

Main():void =
    Print("OVPROBE half {Half}")
