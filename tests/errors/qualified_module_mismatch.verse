# expect: M.(N:)F: N is not the module M
M := module:
    F<public>():int = 1
N := module:
    F<public>():int = 2
Main():void = Print("{M.(N:)F()}")
