# A statement may destructure a tuple, `(X:t, _, Z:u) = e`, when at least
# one element is named (Book of Verse tests, Tuple.versetest: `(X:int, _,
# Z:string) = MyTuple`): each named element is a definition of the block,
# `_` skips one, and e is evaluated once.
Pair():tuple(int, string, float) = (7, "seven", 7.5)
Main():void =
    var Calls:int = 0
    (A:int, _, C:float) = block:
        set Calls += 1
        Pair()
    {
        (D:int, E:string) := (1, "one")
        Print("{A} {C} {D} {E} {Calls}")
    }
