# expect: expected AA, found bb_base
# the instance is of the base type (Book of Verse tests,
# GetCastableFinalSuperClass.versetest 101-107, 3509)
bb_base := class<castable> {}
AA := class(bb_base) {}
Main():void =
    if (GetCastableFinalSuperClass[AA, bb_base{}]) then Print("found")
