# A body after ':' may be empty wherever one may be written, as {} may: its
# next line is no deeper than its construct (Book of Verse tests: an empty
# class<concrete>:, an empty then:).
marker := class<concrete>:
    # only a comment: the class is empty
point := struct:
shape := interface:
color := enum:
square := class(shape):
    Side:int = 2

M := module:
    c<public> := class:
    X<public>:int = 1

counter := class:
    Count:int = 7
MakeCounter<constructor>() := counter:

Main():void =
    A := marker{}
    P := point{}
    S := square{}
    var Num:int = 1
    if (Num = 1):
    if (Num = 2) then:
    else:
    if (Num = 1; set Num = 42)
    then:  # an empty then
    for (I := 1..3):
    loop:
        break
    block:
    Print("{Num} {M.X} {S.Side} {MakeCounter().Count}")
