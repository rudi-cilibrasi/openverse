# expect: 9:20: 'X' is ambiguous: both A.X and B.X are open
A := module:
    X<public>:int = 1
B := module:
    X<public>:int = 2
C := module:
    using{A}
    using{B}
    Y<public>:int = X
Main():void = Print("{C.Y}")
