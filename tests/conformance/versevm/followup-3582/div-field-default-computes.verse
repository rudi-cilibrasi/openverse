# 3582 follow-up (#724): a class field whose default calls a <computes>
# function.
Count()<computes>:int = 3

thing := class:
    Size:int = Count()

Main():void =
    T := thing{}
    Print("OVPROBE size {T.Size}")
