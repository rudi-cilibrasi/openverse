# 3582 follow-up (#724), compile only: a module constant defined by a tuple
# of literals. OpenVerse admits it and prints "second 2".
Pair:tuple(int, int) = (1, 2)

Main():void =
    Print("OVPROBE second {Pair(1)}")
