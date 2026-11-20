# Enums as map keys: insertion order kept, lookups, and counting into a map.
# Tests LANGUAGE.md, Maps: "for (K -> V : M) in insertion order"; enums are
# comparable (Comparability: "enums").
# OpenVerse prints (Lean and C agree):
#   plum 3 | apple 1 | pear 1
fruit := enum:
    Apple
    Pear
    Plum

Name(F:fruit):string =
    case (F):
        fruit.Apple => "apple"
        fruit.Pear => "pear"
        fruit.Plum => "plum"

Main():void =
    Basket:[]fruit = array{fruit.Plum, fruit.Apple, fruit.Plum, fruit.Pear, fruit.Plum}
    var Counts:[fruit]int = map{}
    for (F : Basket):
        if (set Counts[F] = (Counts[F] or 0) + 1) {}
    for (F -> N : Counts):
        Print("OVPROBE {Name(F)} {N}")
