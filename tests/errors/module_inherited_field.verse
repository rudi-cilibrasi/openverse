# expect: 6:4: 'Y' is already defined (as M.Y); Verse does not allow shadowing
p := class:
    Y:int = 7
M := module:
    Y:int = 100
    c<public> := class(p):
        Get<public>():int = Y
Main():void = Print("{M.c{}.Get()}")
