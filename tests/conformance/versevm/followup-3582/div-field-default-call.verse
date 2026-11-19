# 3582 follow-up (#724): a class field whose default calls a function
# without specifiers.
Count():int = 3

thing := class:
    Size:int = Count()

Main():void =
    T := thing{}
    Print("OVPROBE size {T.Size}")
