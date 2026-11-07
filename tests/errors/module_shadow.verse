# expect: 6:4: 'X' is already defined (as m.X); Verse does not allow shadowing
m := module:
    X<public>:int = 1
using{m}
Main():void =
    X := 5
    Print("{X}")
