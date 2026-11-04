# Maps (Book of Verse ch. 3 "Containers", ch. 5 "Mutability").
Main():void =
    var Friendliness:[string]int = map{"peach" => 1000}
    set Friendliness["pelican"] = 17
    if (set Friendliness["peach"] += 2000) {}   # += can fail (missing key): a failure context
    if (not (set Friendliness["tomato"] += 1000)) { Print("tomato is not a key, so += fails") }
    if (P := Friendliness["peach"]) { Print("peach: {P}") }
    if (not Friendliness["car"]) { Print("lookup of a missing key fails") }
    Print("{Friendliness.Length} entries")
    for (K -> V : Friendliness) { Print("{K} => {V}") }
    # duplicate keys in a literal: the last value wins, at the last position
    M := map{1 => "a", 2 => "b", 1 => "c"}
    for (K -> V : M) { Print("{K}: {V}") }
    if (M = map{2 => "b", 1 => "c"}) { Print("map equality is order-sensitive and holds here") }
    if (not (M = map{1 => "c", 2 => "b"})) { Print("...and fails in the other order") }
    Total := for (V : map{"x" => 3, "y" => 4}) { V * 10 }
    for (T : Total) { Print("{T}") }
