# expect: 4:23: module m has no member Missing
m := module:
    X<public>:int = 2
Main():void = Print("{m.Missing}")
