# `set P op= e` evaluates P's indices and keys, then e, then reads P's old
# value and writes P (the Book of Verse's tests, ArrayAppend.versetest 140 and
# 183: what e does to P is seen): it is `set P = P op v`, v e's value
pair := struct:
    Xs:[]int = array{}
    K:int = 0
cell := class:
    var V:int = 1
    var Arr:[]int = array{1, 2}

Log(S:string, N:int):int =
    Print(S)
    N

Main()<decides>:void =
    var N:int = 5
    set N += (set N = 100; 1)
    Print("var {N}")
    var Xs:[]int = array{1, 2, 3}
    set Xs += (set Xs = array{0}; array{42})
    Print("array var {Xs.Length} {Xs[0]} {Xs[1]}")
    var S:pair = pair{Xs := array{1, 2, 3}}
    set S.Xs += (set S.Xs = array{0}; array{42})
    Print("struct field {S.Xs.Length} {S.Xs[0]}")
    # (e's write to another field is kept: P is rebuilt from what e left)
    set S.Xs += (set S.K = 9; array{7})
    Print("struct other field {S.K} {S.Xs.Length}")
    var M:[int][]int = map{42 => array{}}
    set M[42] += (set M[42] = array{0}; array{42})
    Print("map entry {M[42].Length} {M[42][0]}")
    var A:[]int = array{1, 2, 3}
    set A[0] += (set A[0] = 50; set A[1] = 60; 10)
    Print("array element {A[0]} {A[1]}")
    C := cell{}
    set C.V *= (set C.V = 7; 3)
    Print("object field {C.V}")
    set C.Arr[1] += (set C.Arr = array{8, 9}; 1)
    Print("object path {C.Arr[0]} {C.Arr[1]}")
    # (the indices first, once, then e, then the old value)
    var B:[]int = array{0, 0}
    set B[Log("index", 1)] += Log("value", 4)
    Print("indexed {B[1]}")
    # (a key missing when e has run: the set fails, and e is rolled back with it)
    var Q:[int]int = map{1 => 1}
    if (set Q[2] += (set Q[1] = 5; 1)) then Print("set") else Print("missing key {Q[1]}")
