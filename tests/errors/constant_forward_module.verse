# expect: the value of the constant settings.Low names settings.High, which is defined after it in the same scope
# Within a module too: Low is defined before High, its module's constant.
settings := module:
    Low<public>:int = High - 1
    High<public>:int = 10
Main():void = Print("{settings.Low}")
