# expect: 4:4: expected an indented function body
M := module:
    F<public>():int =
    1
Main():void = Print("{M.F()}")
