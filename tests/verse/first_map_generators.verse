# first takes a map's entries as for does (Book of Verse ch. 7, "first": "The
# `first` expression uses the same binding syntax as `for`"; "Maps can be
# iterated over in two ways: values only, or key-value pairs"): V : M its
# values, K -> V : M its keys and values, in the order of the map; what a
# failed entry's clauses did is undone, and the first entry whose clauses
# succeed gives the body's value. Strings and ranges as for's.
counter := class:
    var N:int = 0
    Inc()<transacts><decides>:void =
        set N += 1

KeyOf(M:[string]int, Want:int)<transacts><decides>:string =
    first(K -> V : M; V = Want){K}

Main():void =
    M:[int]int = map{1 => 10, 2 => 10, 3 => 20}
    # the last entry is reached, and a key is no index
    if (X := first{K -> V : M; V > 15; K}) then Print("key {X}") else Print("no key")
    if (X := first{V : M; V > 15; V}) then Print("value {X}") else Print("no value")
    if (X := first{K -> V : M; K}) then Print("first key {X}")
    if (not first{K -> V : M; V > 25; K}) then Print("none above 25")
    # keys of another type
    Names:[string]int = map{"Ada" => 3, "Bo" => 7, "Cy" => 7}
    if (N := KeyOf[Names, 7]) then Print("seven: {N}")
    if (not KeyOf[Names, 8]) then Print("no eight")
    Empty:[int]int = map{}
    if (not first{V : Empty; V > 0; V}) then Print("empty")
    # a failed entry's effects undone
    C := counter{}
    if (X := first{K -> V : M; C.Inc[]; V > 15; K}) then Print("found {X}, count {C.N}")
    D := counter{}
    if (not first{K -> V : M; D.Inc[]; V > 25; K}) then Print("not found, count {D.N}")
    # nested generators: a map's arrays
    Lists:[string][]int = map{"a" => array{1, 2}, "b" => array{3, 4}}
    if (P := first{K -> Xs : Lists; E : Xs; E > 2; (K, E)}) then Print("pair {P(0)} {P(1)}")
    if (P := first{E : array{5, 6}; K -> V : M; V = E + 5; (E, K)}) then Print("pair {P(0)} {P(1)}")
    # a string's characters, a range's ints, as for's
    if (Ch := first{Ch2 : "verse"; Ch2 = 'r'; Ch2}) then Print("char {Ch}")
    if (At := first{J -> Ch3 : "verse"; Ch3 = 's'; J}) then Print("index {At}")
    if (R := first{Y := 1..9; Y * Y > 20; Y}) then Print("range {R}")
