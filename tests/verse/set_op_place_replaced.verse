# set P op= e on a path from a local var resolves P's place before e runs:
# P's keys, once, and the container P's last step writes into (#704). When e
# replaces that container, or one above it on P, the old value is read from
# the container e replaced and the new one written into it, so the variable
# keeps what e left; when e only writes into it, e's writes are seen.
#
# Epic's VerseVM, UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM", run 2026-11-18), prints a row of length 1 holding 0 for the
# first case below (tests/conformance/versevm/compound-indexed-write.verse),
# as the Book of Verse's VerseVM test ArrayAppend.versetest:12 expects, and
# length 2 for the whole-variable control, as ArrayAppend.versetest:7 does
# (compound-whole-write.verse). The other shapes follow the same rule and are
# not yet checked on Epic: probes for them are in tests/conformance/versevm.
pair := struct<computes>:
    N:int = 0
    Xs:[]int = array{}

cell := class:
    var V:int = 1

Id(N:int):int = N

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

Ns(Ps:[]pair):[]int = for (P : Ps) { P.N }

Main()<transacts>:void =
    # (Epic, and the Book's VerseVM test: the variable replaced)
    var Rows:[][]int = array{array{1, 2, 3}}
    if (set Rows[0] += if (set Rows = array{array{0}}; 0 = 0) then array{42} else array{42}):
        Print("variable replaced {ShowRows(Rows)}")
    # (Epic, and the Book's: a whole variable is its own place)
    var Row:[]int = array{1, 2, 3}
    set Row += if (set Row = array{0}; 0 = 0) then array{42} else array{42}
    Print("whole variable {ShowInts(Row)}")
    # (the element written in place, as ArrayAppend.versetest:183 does a
    # map's entry: seen)
    var Same:[][]int = array{array{1, 2, 3}}
    if (set Same[0] += if (set Same[0] = array{0}; 0 = 0) then array{42} else array{42}):
        Print("element written in place {ShowRows(Same)}")
    # nested indices: the variable, the row (its key written or computed),
    # another row, and the row written in place
    var G:[][]int = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G = array{array{0, 0}, array{7, 7}}; 0 = 0) then 10 else 10):
        Print("nested, variable replaced {ShowRows(G)}")
    set G = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G[1] = array{9, 9}; 0 = 0) then 10 else 10):
        Print("nested, row replaced {ShowRows(G)}")
    set G = array{array{1, 2}, array{3, 4}}
    if (set G[Id(1)][0] += if (set G[Id(1)] = array{9, 9}; 0 = 0) then 10 else 10):
        Print("nested, row replaced by key {ShowRows(G)}")
    set G = array{array{1, 2}, array{3, 4}}
    if (set G[Id(1)][0] += if (set G[Id(0)] = array{5}; 0 = 0) then 10 else 10):
        Print("nested, other row replaced {ShowRows(G)}")
    set G = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G[1][0] = 100; set G[1][1] = 200; 0 = 0) then 10 else 10):
        Print("nested, row written in place {ShowRows(G)}")
    # a map's entry, the map replaced
    var M:[int]int = map{1 => 10, 2 => 20}
    if (set M[1] += if (set M = map{1 => 100}; 0 = 0) then 1 else 1):
        Print("map replaced {M[1] or -1} {M.Length}")
    # a struct's field, the struct replaced
    var S:pair = pair{N := 1, Xs := array{1}}
    set S.N += if (set S = pair{N := 50}; 0 = 0) then 5 else 5
    Print("struct replaced {S.N} {ShowInts(S.Xs)}")
    # a struct's field in an array: the array replaced, the element replaced,
    # the element's other field written in place
    var Ps:[]pair = array{pair{N := 1}, pair{N := 2}}
    if (set Ps[1].N += if (set Ps = array{pair{N := 30}, pair{N := 40}}; 0 = 0) then 5 else 5):
        Print("struct in array, array replaced {ShowInts(Ns(Ps))}")
    set Ps = array{pair{N := 1}, pair{N := 2}}
    if (set Ps[1].N += if (set Ps[1] = pair{N := 70}; 0 = 0) then 5 else 5):
        Print("struct in array, element replaced {ShowInts(Ns(Ps))}")
    set Ps = array{pair{N := 1}, pair{N := 2}}
    if (set Ps[1].N += if (set Ps[1].Xs = array{9}; 0 = 0) then 5 else 5, P1 := Ps[1]):
        Print("struct in array, other field {ShowInts(Ns(Ps))} {ShowInts(P1.Xs)}")
    # the other operators, and one written in place
    var Is:[]int = array{10}
    if (set Is[0] -= if (set Is = array{100}; 0 = 0) then 1 else 1):
        Print("-= {ShowInts(Is)}")
    if (set Is[0] *= if (set Is = array{200}; 0 = 0) then 2 else 2):
        Print("*= {ShowInts(Is)}")
    if (set Is[0] -= if (set Is[0] = 300; 0 = 0) then 1 else 1):
        Print("-= in place {ShowInts(Is)}")
    var Fs:[]float = array{1.5}
    if (set Fs[0] *= if (set Fs = array{4.0}; 0 = 0) then 2.0 else 2.0, F := Fs[0]):
        Print("float *= {F}")
    if (set Fs[0] /= if (set Fs = array{8.0}; 0 = 0) then 2.0 else 2.0, F := Fs[0]):
        Print("float /= {F}")
    # the value of the set: the new value, from the replaced container as e
    # left it when it replaced it
    var P:[][]int = array{array{1}}
    if (V := (set P[0] += (set P[0] = array{5}; set P = array{array{0}}; array{42}))):
        Print("value {ShowInts(V)} {ShowRows(P)}")
    # an object on the path is the one the path names before e (#34): the
    # write goes to it, also when e replaces the variable
    C1 := cell{V := 1}
    var O:cell = C1
    set O.V += if (set O = cell{V := 100}; 0 = 0) then 5 else 5
    Print("object replaced {C1.V} {O.V}")
    C2 := cell{V := 1}
    var Cs:[]cell = array{C2}
    if (set Cs[0].V += if (set Cs = array{cell{V := 50}}; 0 = 0) then 5 else 5, Now := Cs[0]):
        Print("object in array, array replaced {C2.V} {Now.V}")
