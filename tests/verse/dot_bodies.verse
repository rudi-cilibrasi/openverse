# A body may be written as `.` and an expression on its line, wherever `:` or
# `{…}` may be (Book of Verse tests: `if (1 < 2). set Num = 42`,
# `for(n:nums). set curSum += n`, `spawn. F()`).
F(Xs:[]int):int =
    var S:int = 0
    for (X:Xs). set S += X
    S
G()<suspends>:void = {}
Main():void =
    var Num:int = 123
    if (1 < 2). set Num = 42 else. set Num = 56
    set Num = if (1 > 2). Num else if (3 > 4). 56 else. Num + 1
    loop. break
    spawn. G()
    block. Print("{F(array{1, 2, 3})} {Num}")
