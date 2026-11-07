# ConcatenateMaps (Book of Verse ch. 9): every map's entries, a later map's
# value winning for a key, which keeps its first position

Show(M:[string]int):string =
    var S:string = ""
    for (K -> V : M) { set S = "{S}{K}={V} " }
    S

Main():void =
    A := map{"a" => 1, "b" => 2}
    B := map{"b" => 20, "c" => 30}
    C := map{"c" => 300, "d" => 400}
    Print(Show(ConcatenateMaps(A, B)))
    Print(Show(ConcatenateMaps(A, B, C)))
    Print(Show(ConcatenateMaps(A)))
    Print(Show(ConcatenateMaps(A, map{})))
    E:[string]int = ConcatenateMaps(map{}, B)
    Print(Show(E))
    N := ConcatenateMaps(map{1 => "x"}, map{2 => "y", 1 => "z"})
    for (K -> V : N) { Print("{K}:{V}") }
    Print("{A.Length} {ConcatenateMaps(A, B, C).Length}")
