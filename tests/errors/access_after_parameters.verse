# expect: <public> after the parameters of Twice: an access specifier is written on the name, Twice<public>(…)
Tools := module:
    Twice(X:int)<public>:int = 2 * X
Main():void = Print("{Tools.Twice(2)}")
