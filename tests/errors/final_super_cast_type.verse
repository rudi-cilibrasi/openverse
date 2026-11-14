# expect: expected DD, found WW
# a cast through the result gives a value of the base type (Book of Verse
# tests, GetCastableFinalSuperClass.versetest 137-145)
WW := class<castable> {}
DD := class<final_super>(WW) {}
F()<decides>:void =
    D:DD = DD{}
    TT:castable_subtype(WW) := GetCastableFinalSuperClassFromType[WW, DD]
    E:DD = TT[D]
Main():void = Print("ok")
