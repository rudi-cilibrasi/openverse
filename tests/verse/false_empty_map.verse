# `false` is accepted wherever an empty array or map is expected (Book of
# Verse ch. 2, "void, true, tuple() and false"): it is the empty map.
Count(M:[string]int):int = M.Length

Main():void =
    M:[int]int = false
    Print("{M.Length} {Count(false)}")
    var N:[int]int = map{1 => 2}
    set N = false
    Print("{N.Length}")
    if (N = map{}, M = N) then Print("empty")
