# ConcatenateMaps lays the entries of the first map down, then the second's: a
# key both maps have takes the second map's value at the second map's place
# (the Book of Verse's API reference: "a map keeps only the last value given
# for a key", as map{…} does), and the first map's other keys keep theirs
Keys(M:[string]int):string =
    var S:string = ""
    for (K -> V : M) { set S = "{S}{K}{V}" }
    S

Main():void =
    Print(Keys(ConcatenateMaps(map{"p" => 1, "q" => 2}, map{"q" => 3, "p" => 4})))
    Print(Keys(ConcatenateMaps(map{"p" => 1, "q" => 2, "r" => 3}, map{"p" => 5})))
    Print(Keys(ConcatenateMaps(map{"p" => 1, "q" => 2}, map{"s" => 7, "q" => 8})))
    # (as a literal that gives a key twice)
    Print(Keys(map{"p" => 1, "q" => 2, "q" => 3, "p" => 4}))
    # (equality of maps is order-sensitive)
    if (ConcatenateMaps(map{"p" => 1, "q" => 2}, map{"p" => 1}) = map{"q" => 2, "p" => 1}) then Print("moved")
    # (an update in place keeps a key's place; a concatenation moves it)
    var M:[string]int = map{"a" => 1, "b" => 2, "c" => 3}
    set M["a"] = 9
    Print(Keys(M))
    set M = ConcatenateMaps(M, map{"a" => 0, "d" => 4})
    Print(Keys(M))
