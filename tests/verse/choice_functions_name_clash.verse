# functions with several values (#235), review case b2-name-clash
F(X:int):int =
    var A:int = X | X + 100









    var B:int = X | X + 1000
    A + B
Main():void =
    if (V0 := F(0), V1 := F(1), V2 := F(2), V3 := F(3), V4 := F(4), V5 := F(5), V6 := F(6), V7 := F(7), V8 := F(8), V9 := F(9), V10 := F(10), V11 := F(11)) then Print("{V11}")
