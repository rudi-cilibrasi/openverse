# Definitions on one line are separated by `;` or `,`, at the top level, in
# a module and in a braced module (Book of Verse ch. 1, "Semicolons vs
# Commas"; its tests: `X:int=0, Y:int=0`, `m:=module{X:int=0,Y:int=0}`).
X:int = 1, Y:int = 2; Z:int = 3
M := module{ G<public>():int = 7, H<public>():int = 8; K<public>:int = 9 }
N := module:
    A<public>:int = 10; B<public>:int = 20
Main():void =
    Print("{X + Y + Z} {M.G() + M.H() + M.K} {N.A + N.B}")
