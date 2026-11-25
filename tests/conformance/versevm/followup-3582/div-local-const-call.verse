# 3582 follow-up (#724): a local constant defined by a call of a function
# without specifiers. Control: locals are not data-members.
Count():int = 3

Main():void =
    Limit:int = Count()
    Print("OVPROBE limit {Limit}")
