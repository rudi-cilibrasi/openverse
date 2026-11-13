# expect: 5:4: set through a map's key can fail
# A set through a map's key is <decides> in Verse (the Book of Verse's API reference), so it is in a failure context, though its last key inserts.
Main():void =
    var M:[int]int = map{}
    set M[1] = 2
    Print("{M.Length}")
