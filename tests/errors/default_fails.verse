# expect: the default of ?Y of F can fail: a default is no failure context, also of a <decides> function
F(X:[]int, ?Y:int = X[0]):int = Y
Main():void =
    if (V := F(array{})) then Print("{V}") else Print("fail")
