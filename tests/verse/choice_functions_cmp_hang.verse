# functions with several values (#235), review case b1-cmp-hang
# expected: prints 5 (Small's values: Digit() < 2 passes for 0 and 1 -> 5, 5)
Digit():int = 0 | 1 | 2
Small()<decides>:int =
    Digit() < 2
    5
Main():void =
    for (X := Small[]) { Print("{X}") }
