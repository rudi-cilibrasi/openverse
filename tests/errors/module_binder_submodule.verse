# expect: 9:4: 'B' is already defined (as A.B); Verse does not allow shadowing
A := module:
    B<public> := module:
        X<public>:int = 1
    pt<public> := struct:
        X:int = 5
using{A}
Main():void =
    B := A.pt{}
    Print("{B.X}")
