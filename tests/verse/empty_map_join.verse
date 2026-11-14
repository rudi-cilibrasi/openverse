# A map{} with no type from its context, a [false]false, joins another map
# at that map's type and converts to it (Book of Verse tests, Map.versetest:240).
Main():void =
    M1 := map{}
    M2 := ConcatenateMaps(M1, map{0 => "0"})
    if (M2 = map{0 => "0"}) then Print("joined {M2.Length}")
    M3:[string]int = M1
    Print("{M3.Length}")
