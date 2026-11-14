# weak_map(k, v) (Book of Verse ch. 3, "Weak Maps"; docs/research/weak-map.md):
# a supertype of [k]v that keeps entry access, W[k] and set W[k] = v, and
# rollback. A map is a weak map; keys are covariant (a map of derived keys
# is a weak map of base keys) and a key of a class above the map's keys
# reads (Map.versetest 388). Entries of struct and container values are
# written through paths; a class's var field may be one; so may a local,
# which can be replaced whole.

base := class<unique>:
    Name:string
derived := class(base):
    Extra:int = 0
other := class(base) {}
point := struct:
    X:int
    Y:int
holder := class:
    var Scores:weak_map(base, int) = map{}
    var Cells:weak_map(int, []int) = map{}

Identity(X:t where t:type):t = X
Lookup(W:weak_map(base, int), K:base)<decides>:int = W[K]
Make(K:derived):weak_map(derived, int) = map{K => 7}

Main():void =
    A := derived{Name := "a"}
    B := derived{Name := "b"}
    O := other{Name := "o"}
    # a map of derived keys is a weak map of base keys
    M:[derived]int = map{A => 1, B => 2}
    W:weak_map(base, int) = M
    if (V := Lookup[W, A]) then Print("A {V}") else Print("no A")
    if (V := Lookup[W, O]) then Print("O {V}") else Print("no O")
    W2:weak_map(base, int) = Make(B)
    if (V := W2[B]) then Print("B {V}") else Print("no B")
    # a key of a class above the map's keys reads
    BK:base = A
    WD:weak_map(derived, int) = M
    if (V := WD[BK]) then Print("WD[BK] {V}") else Print("no WD[BK]")
    # (so does one of a map, Map.versetest 394)
    if (V := M[BK]) then Print("M[BK] {V}") else Print("no M[BK]")
    if (not M[O]) then Print("no M[O]")
    # a generic function's value
    Y := Identity(W)
    if (V := Y[B]) then Print("Y[B] {V}") else Print("no Y[B]")
    # struct values: a path through an entry
    var P:weak_map(string, point) = map{}
    if (set P["p"] = point{X := 1, Y := 2}) {}
    if (set P["p"].X = 10) {}
    if (Q := P["p"]) then Print("p {Q.X} {Q.Y}")
    if (set P["p"].Y += 5) {}
    if (Q := P["p"]) then Print("p {Q.X} {Q.Y}")
    # a class's var fields
    H := holder{}
    if (set H.Scores[A] = 3) {}
    if (set H.Cells[1] = array{1, 2, 3}) {}
    if (set H.Cells[1][0] = 99) {}
    if (V := H.Scores[A], C := H.Cells[1][0]) then Print("H {V} {C}")
    if (not H.Scores[B]) then Print("H no B")
    # comparable keys (Map.versetest 464)
    var CK:weak_map(comparable, int) = map{}
    if (set CK[0] = 1, set CK["x"] = 2) {}
    if (V := CK[0], U := CK["x"]) then Print("CK {V} {U}")
    if (not CK[1]) then Print("CK no 1")
    # a weak map of weak maps
    var N:weak_map(int, weak_map(int, int)) = map{1 => map{2 => 3}}
    if (set N[1][4] = 5) {}
    if (V := N[1][2], U := N[1][4]) then Print("N {V} {U}")
    # an option of one
    MaybeW:?weak_map(int, int) = option{map{1 => 1}}
    if (MW := MaybeW?, V := MW[1]) then Print("opt {V}")
    # a failure context undoes a whole replacement and the entries set
    var R:weak_map(int, int) = map{1 => 1}
    if:
        set R = map{2 => 2}
        set R[3] = 3
        R[4]
    if (V := R[1]) then Print("R[1] {V}") else Print("no R[1]")
    if (not R[2], not R[3]) then Print("R rolled back")
