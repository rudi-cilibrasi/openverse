# expect: 7:14: M.c{…} constructs M.c here: the constructor of M.c is internal to M
# Of two uses an access does not admit, the first in the source is refused:
# a parameter's default comes before the function's body (Book of Verse
# ch. 12).
M := module:
    c<public> := class<internal>{A<public>:int = 1}
F(?X:int = M.c{}.A):int = M.c{}.A + X
Main():void = Print("{F()}")
