TupleEarly():int =
    Pair:tuple(int, int) = (loop{return 7}, 9)
    Pair(1)

ArrayEarly():int =
    Values:[]int = array{loop{return 8}, 9}
    Values.Length

Joined(N:int):int =
    if (N = 0) then loop{return 11} else 4

Main():void =
    Print("{TupleEarly()} {ArrayEarly()} {Joined(0)} {Joined(1)}")
