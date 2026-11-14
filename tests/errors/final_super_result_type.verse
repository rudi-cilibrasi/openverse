# expect: expected castable_subtype(BB), found castable_subtype(AA)
# the result is a castable_subtype of the base type, not of the class it
# holds (Book of Verse tests, GetCastableFinalSuperClass.versetest 182-191)
bb_base := class<castable> {}
AA := class(bb_base) {}
BB := class<final_super>(AA) {}
Main():void =
    D:BB = BB{}
    if (TT:castable_subtype(BB) = GetCastableFinalSuperClass[AA, D]) then Print("found")
