# set through a call's result or a construction: the root first, bound to
# a name of its own, then the keys, then the value (the Book's tests,
# AssignmentSequencing.versetest 17-48, FORT-779650 27); a key of several
# values is a tuple's (Map.versetest:472).
int_ref := class:
    var Contents:int = 0
int_map_ref := class:
    var Contents:[int]int = map{}
Effectful(Ref:int_ref, X:t where t:type):t =
    set Ref.Contents += 1
    X
Main():void =
    X := int_ref{}
    Y := int_ref{}
    set Effectful(Y, X).Contents = Y.Contents
    Print("{X.Contents}")
    Z := set Effectful(Y, X).Contents = Y.Contents + 10
    Print("{X.Contents} {Z}")
    M := int_map_ref{}
    W := int_ref{Contents := 3}
    # (a set through a map's key can fail: in a failure context)
    if (set Effectful(Y, M).Contents[Effectful(W, Y.Contents)] = (if (V := M.Contents[3]) then 1 else W.Contents)) then Print("set")
    if (V := M.Contents[3]) then Print("{V} {Y.Contents} {W.Contents}")
    Q := set int_ref{Contents := 2}.Contents += 5
    Print("{Q}")
    var T:[tuple(int, int)]int = map{}
    if (set T[1, 2] = 7, V := T[(1, 2)]) then Print("{V}")
