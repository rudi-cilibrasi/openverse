# Nested failure contexts: an inner one fails and the outer goes on; the
# inner succeeds and the outer then fails, undoing both.
# Tests LANGUAGE.md, Failure: "failure contexts (if conditions, for clauses,
# option{}, logic{}, not, left of or, <decides> bodies) with rollback of var
# writes"; ch. 8: provisional changes become permanent only if the entire
# context succeeds.
# OpenVerse prints (Lean and C agree):
#   inner fails 0 1 | outer fails 0 1 | not 0 2 | or 0 0 0
Main():void =
    var X:int = 0
    var Y:int = 0
    if (O := option{set X += 1; X > 5}, set Y += 1, Y > 0) {}
    Print("OVPROBE inner fails {X} {Y}")
    if (O := option{set X += 10; X > 5}, set Y += 100, Y > 1000) {}
    Print("OVPROBE outer fails {X} {Y}")
    if (not (set X = 50; X < 10), set Y = 2) {}
    Print("OVPROBE not {X} {Y}")
    Z:int = (set X = 7; X > 10) or (set Y = X; 0)
    Print("OVPROBE or {X} {Y} {Z}")
