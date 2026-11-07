# expect: the default of ?Y of F can fail, but F is not <decides>
F(X:[]int, ?Y:int = X[0]):int = Y
Main():void =
    if (V := F(array{})) then Print("{V}") else Print("fail")
