# Nested set paths (#16; Book of Verse §3.5, §9.3): set on a path rebuilds the
# variable's value. An index out of range, or an intermediate map key that is
# missing, makes the set fail, and the failure is rolled back.

vector2 := struct:
    X:int = 0
    Y:int = 0

player := struct:
    Name:string
    Pos:vector2 = vector2{}
    Scores:[]int = array{}

ShowInts(Items:[]int):string =
    var S:string = ""
    for (I -> X : Items):
        if (I > 0) then set S += ", "
        set S += ToString(X)
    "[{S}]"

Main():void =
    # field, field
    var P:player = player{Name := "Ana", Scores := array{1, 2, 3}}
    set P.Pos.X = 4
    set P.Pos.Y += 7
    Print("({P.Pos.X}, {P.Pos.Y})")
    # field, index
    if (set P.Scores[1] = 20) then Print(ShowInts(P.Scores))
    if (set P.Scores[2] *= 10) then Print(ShowInts(P.Scores))
    # index, index
    var Grid:[][]int = array{array{0, 0}, array{0, 0}}
    if (set Grid[1][0] = 5, set Grid[0][1] += 2, G0 := Grid[0], G1 := Grid[1]) then Print("{ShowInts(G0)} {ShowInts(G1)}")
    # index, field
    var Ps:[]vector2 = array{vector2{}, vector2{X := 1}}
    if (set Ps[1].Y = 9, Q := Ps[1]) then Print("({Q.X}, {Q.Y})")
    # map key, index; key, key
    var Stock:[string][]int = map{"apples" => array{1, 2}}
    if (set Stock["apples"][1] = 7, A := Stock["apples"]) then Print("apples {ShowInts(A)}")
    var Nested:[string][string]int = map{"a" => map{"x" => 1}}
    # the last key inserts
    if (set Nested["a"]["y"] = 2, Na := Nested["a"]) then Print("a has {Na.Length} keys")
    # failures roll back the whole set
    if (set Grid[5][0] = 1) then Print("unreachable") else Print("row 5 is out of range")
    if (set Stock["pears"][0] = 1) then Print("unreachable") else Print("no pears")
    if (set Nested["b"]["x"] = 1) then Print("unreachable") else Print("no b")
    if (set P.Scores[9] = 0) then Print("unreachable")
    Print("{Stock.Length} key(s), {Nested.Length} key(s), {P.Scores.Length} scores")
    # the value of a set is the new leaf value
    if (V := (set Grid[0][0] = 42)) then Print("set gave {V}")
