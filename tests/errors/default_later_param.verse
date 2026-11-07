# expect: unknown identifier 'Y'
F(?X:int = Y, ?Y:int = 1):int = X + Y
Main():void = Print("{F()}")
