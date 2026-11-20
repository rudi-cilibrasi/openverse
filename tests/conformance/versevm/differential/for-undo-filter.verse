# What a for undoes: a write in a clause whose iteration a later filter
# rejects, and writes made by clauses after the last value that reached the
# body.
# Tests LANGUAGE.md, Readings, "What a for undoes": "its clauses are one
# search: what they did since the last value that reached the body is kept
# at the body and undone when the search ends; a failure undoes back to its
# own element"; the Book's FlowControl/for.versetest 317-392, 08_failure.md:92
# ("a failure context for each iteration"). If clause writes were kept,
# a would be 15, b 30 and c 203.
# OpenVerse prints (Lean and C agree):
#   a 12 3 | b 10 1 | c 202 2
Main():void =
    var T:int = 0
    R := for (X := 1..5, (set T += X; X > 2)) { X }
    Print("OVPROBE a {T} {R.Length}")
    var U:int = 0
    S := for (X := 1..3, (set U += 10; X < 2)) { X }
    Print("OVPROBE b {U} {S.Length}")
    var V:int = 0
    W := for (X := 1..3, (set V += 1; X > 1)):
        set V += 100
        X
    Print("OVPROBE c {V} {W.Length}")
