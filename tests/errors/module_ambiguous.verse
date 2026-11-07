# expect: 8:22: 'Shown' is ambiguous: both m.Shown and n.Shown are open
m := module:
    Shown<public>:int = 2
n := module:
    Shown<public>:int = 4
using{m}
using{n}
Main():void = Print("{Shown}")
