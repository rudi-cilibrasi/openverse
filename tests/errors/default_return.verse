# expect: return is not allowed in a parameter's default
F(X:int, ?Y:int = block{ return X }):int = Y
M():int =
    V := F(7)
    V + 1
Main():void = Print("{M()}")
