# Map lookups with struct and option keys built separately from the stored
# key (hashing mismatches were reported on the new Verse VM before 43.10).
pair := struct:
    A:int
    B:?int

Main():void =
    var ByPair:[pair]int = map{}
    if (set ByPair[pair{A := 1, B := option{2}}] = 7) {}
    if (V := ByPair[pair{A := 1, B := option{2}}]):
        Print("OVPROBE struct key found {V}")
    else:
        Print("OVPROBE struct key missing")
    var ByOption:[?int]int = map{}
    if (set ByOption[option{3}] = 8) {}
    if (W := ByOption[option{3}]):
        Print("OVPROBE option key found {W}")
    else:
        Print("OVPROBE option key missing")
    if (X := ByOption[false]):
        Print("OVPROBE empty option key found {X}")
    else:
        Print("OVPROBE empty option key missing")
