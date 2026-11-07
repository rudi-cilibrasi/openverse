# expect: Area<override> does not override an inherited method
square := class:
    Area<override>():int = 1
Main():void = Print("x")
