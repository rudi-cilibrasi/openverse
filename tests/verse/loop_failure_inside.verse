# A loop's body is no failure context, also in a <decides> function (Book of
# Verse tests, SOL-4199-BreakFromIf.versetest:79): what may fail in it is in
# a failure context of its own; the function fails after the loop.
First(Xs:[]int, Min:int)<decides>:int =
    var I:int = 0
    var Found:?int = false
    loop:
        if (I >= Xs.Length) then break
        if (X := Xs[I], X > Min):
            set Found = option{X}
            break
        set I += 1
    Found?
c := class{X:?int = option{option{1}?}}
Main():void =
    if (V := First[array{1, 5, 9}, 4]) then Print("{V}") else Print("none")
    if (V := First[array{1, 2}, 4]) then Print("{V}") else Print("none")
    if (V := c{}.X?) then Print("{V}")
