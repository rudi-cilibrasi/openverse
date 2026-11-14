# false as a type: the type with no value, below every type (Book of Verse
# ch. 2; its tests, 2026-01-26-FindFirstAsyncSubExprMissingOverrides.versetest,
# ParametricTypes.versetest:711): a function that never returns, an array of
# no elements that converts to every array type.
Stop(Message:string):false = Err(Message)
Pick(C:logic):int = if (C?) then 7 else Stop("not picked")
Main():void =
    Print("{Pick(true)}")
    E:[]false = array{}
    I:[]int = E
    Print("{E.Length} {I.Length}")
