# set P op= e whose e replaces P's container (#704, set_op_place_replaced):
# a failure undoes the replacement and the write together; the keys run
# once, before e; the old value's read fails when the replaced container has
# no such element, though the variable has one, and succeeds when the
# replaced container has it, though the variable does not; a choice in e,
# and a loop in e, record the replacement as any write does, and a write that
# a break leaves does not replace anything. Epic's VerseVM, UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086, "Use Verse VM", 2026-11-18), gives
# the results of the cases marked (Epic) for the same bodies
# (tests/conformance/versevm/compound-indexed-control.verse,
# compound-replaced-length.verse).
pair := struct<computes>:
    N:int = 0

Id(N:int):int = N

Log(S:string, N:int):int =
    Print(S)
    N

ShowInts(Items:[]int):string =
    var S:string = ""
    for (I -> X : Items):
        if (I > 0) then set S += ", "
        set S += ToString(X)
    "[{S}]"

ShowRows(Rows:[][]int):string =
    var S:string = ""
    for (I -> Row : Rows):
        if (I > 0) then set S += " "
        set S += ShowInts(Row)
    "[{S}]"

Main()<transacts>:void =
    # (Epic: a later clause fails: the replacement and the write are undone)
    var Rows:[][]int = array{array{1, 2, 3}}
    if (set Rows[0] += if (set Rows = array{array{0}}; 0 = 0) then array{42} else array{42}, Rows.Length = 5):
        Print("unreachable")
    Print("failed later {ShowRows(Rows)}")
    # (e fails after replacing the variable)
    Xs:[]int = array{1}
    if (set Rows[0] += (set Rows = array{array{0}}; array{Xs[Id(3)]})):
        Print("unreachable")
    else:
        Print("right side failed {ShowRows(Rows)}")
    # (Epic: the replaced container has no row 0, the new one has)
    var Short:[][]int = array{}
    if (set Short[0] += if (set Short = array{array{0}}; 0 = 0) then array{42} else array{42}):
        Print("unreachable")
    else:
        Print("no row in the replaced array {ShowRows(Short)}")
    # (Epic: the replaced container has row 0, the new one has not)
    var Long:[][]int = array{array{1}}
    if (set Long[0] += if (set Long = array{}; 0 = 0) then array{42} else array{42}):
        Print("row in the replaced array {ShowRows(Long)}")
    # (the keys once, before e, as Epic runs an index once; then e's own
    # write's keys)
    var G:[][]int = array{array{1}, array{2}}
    if (set G[Log("row", 1)][Log("column", 0)] +=
            if (set G[Log("replaced row", 1)] = array{8}; 0 = 0) then Log("value", 3) else 0):
        Print("keys once {ShowRows(G)}")
    # (a choice in e: an alternative that fails is undone with its
    # replacement, and the next starts from the variable as it was)
    var Y:[]int = array{1}
    if (set Y[0] += ((set Y = array{7}; 1) | 2), Y0 := Y[0], Y0 = 7):
        Print("first alternative {ShowInts(Y)}")
    set Y = array{1}
    if (set Y[0] += ((set Y = array{7}; 1) | 2), Y0 := Y[0], Y0 = 3):
        Print("second alternative {ShowInts(Y)}")
    # (e replaces the variable in a loop, and once more after a failure there)
    var L:[]int = array{1, 1}
    if (set L[1] += (for (I := 0..2) { set L = array{I, I} }; 10)):
        Print("replaced in a loop {ShowInts(L)}")
    set L = array{1, 1}
    if (set L[1] += (if (set L = array{5, 5}, L.Length = 9) then 0 else 10)):
        Print("replacement undone {ShowInts(L)}")
    # (a break leaves e's write before it replaces the variable, or after)
    var Sb:pair = pair{N := 1}
    set Sb.N += (loop:
            set Sb = (if (Sb.N > 0) then break else pair{N := 9})
        10)
    Print("break before the replacement {Sb.N}")
    var Sa:pair = pair{N := 1}
    set Sa.N += (loop:
            set Sa = pair{N := 9}
            break
        10)
    Print("break after the replacement {Sa.N}")
