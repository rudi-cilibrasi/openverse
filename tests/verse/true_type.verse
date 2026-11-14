# `true` as a type (Book of Verse ch. 2, "void, true, tuple() and false"):
# the type of the empty value alone, as tuple() is, below logic; void and
# true interchange inside options, arrays and maps (Tests/Void.versetest
# 50-80, 177-221).
VoidOutput(:int):void = {}
TrueOutput(:int):true = {}
TrueInput(:true):int = 42
VoidInput(:void):int = 19
Erase(X:void):true = X

Main():void =
    Flag:true = false
    AsLogic:logic = Flag
    if (Flag = false, AsLogic = false) then Print("flag")
    MaybeVoid:?void = option{0}
    MaybeTrue:?true = MaybeVoid
    if (MaybeTrue?) then Print("maybe")
    Voids:[]void = array{1, 2, 3}
    Trues:[]true = Voids
    Print("{Trues.Length}")
    VoidMap:[int]void = map{0 => 1, 2 => 3}
    TrueMap:[int]true = VoidMap
    Print("{TrueMap.Length}")
    if (TrueOutput(0) = false, VoidOutput(1) = false) then Print("outputs")
    Q:logic = false
    Print("{TrueInput(false)} {VoidInput(false)}")
    E:true = Erase(5)
    if (E = false) then Print("erased")
    L:logic = if (Q?) then () else true
    if (L?) then Print("logic")
    M:logic = if (Q?) then true else ()
    if (not M?) then Print("empty")
