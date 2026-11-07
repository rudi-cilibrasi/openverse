# expect: 5:0: A.B is internal to A: mark it <public> to use it outside
A := module:
    B := module:
        X<public>:int = 1
using{A.B}
Main():void = Print("{X}")
