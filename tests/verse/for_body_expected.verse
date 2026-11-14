# A for whose values are not of the element type expected has its body at
# that type, as a typed binding has: `false` there is an empty option (the
# Book's tests, Bugs/SOL-4137-MemoryLeakCreatingA3dArray.versetest).
c := class:
    var Data:[][][]?int =
        for (X := 0..1):
            for (Y := 0..2):
                for (Z := 0..2):
                    false
Cube():[][][]?int =
    for (X := 0..1):
        for (Y := 1..1):
            for (Z := 1..1):
                false
Main():void =
    C := c{}
    Print("{C.Data.Length} {Cube().Length}")
    Options:[]?int = for (I := 0..2) { false }
    Print("{Options.Length}")
    for (O : Options, not O?) { Print("empty") }
